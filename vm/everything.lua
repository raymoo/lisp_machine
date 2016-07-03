local lpeg = require("lpeg")
local P, R, S, C, Cs, Cc = lpeg.P, lpeg.R, lpeg.S, lpeg.C, lpeg.Cs, lpeg.Cc
local Cg, Cp = lpeg.Cg, lpeg.Cp
local lpeg_match = lpeg.match

local vm = {}

-- *** Values ***
-- Mappings from scheme types to representations;
--   Number => Lua Number
--   Boolean => Lua Boolean
--   Pair => val_pair
--   "Compiled Pair" => val_compair
--   Symbol => val_symbol
--   Character => val_char
--   String => Lua String
--   Vector => val_vector
--   Empty List => val_empty

-- ** Size standards (Lua types) **
--  Number: 2
--  Boolean: 1
--  String: length + 1
--  Table: 3 + number of keys + sum of the sizes of its values

local ceil = math.ceil

-- Don't give it userdata or threads.
-- Sizes are used in calculating memory use and estimating computational cost.
local function size_of_val(val)
	local v_type = type(val)

	if v_type == "number" then
		return 2
	elseif v_type == "boolean" then
		return 1
	elseif v_type == "string" then
		return #val
	else -- v_type == "table"
		return val.size
	end
end

-- Representations for table-represented types
local function val_symbol(s)
	return {
		tag = "symbol",
		symbol = s,
		size = #s + 16,
	}
end

local function val_char(c)
	return {
		tag = "char",
		char = c,
		size = 15,
	}
end

-- "Compiled" pairs. Takes two sexps rather than addresses. This is used in the
-- internal representation of expressions.
local function val_compair(exp1, exp2)
	return {
		tag = "compair",
		car = exp1,
		cdr = exp2,
		size = 16 + size_of_val(exp1) + size_of_val(exp2),
	}
end

-- Takes the address of the car and cdr
local function val_pair(addr1, addr2)
	return {
		tag = "pair",
		car = addr1,
		cdr = addr2,
		size = 18,
	}
end

-- Takes a list (table) of addresses
local function val_vector(addrs)
	return {
		tag = "vector",
		elements = addrs,
		size = 18 + #addrs * 2,
	}
end

local the_empty = {
	tag = "empty",
	size = 13,
}

local function val_empty()
	return the_empty
end

-- *** Non-Value Tokens ***
local tok_lparen = {}
local tok_rparen = {}
local tok_vecstart = {}
local tok_bytevecstart = {}
local tok_quote = {}
local tok_backquote = {}
local tok_unquote = {}
local tok_unquote_splice = {}
local tok_dot = {}

local unvalue_toks = {
	[tok_lparen] = "lparen",
	[tok_rparen] = "rparen",
	[tok_vecstart] = "vecstart",
	[tok_bytevecstart] = "bytevecstart",
	[tok_quote] = "quote",
	[tok_backquote] = "backquote",
	[tok_unquote] = "unquote",
	[tok_unquote_splice] = "unquote-splice",
	[tok_dot] = "dot",
}

local function is_value_tok(tok)
	return not unvalue_toks[tok]
end

-- *** Lexer ***
-- Mostly copied from the R7RS report

local intraline_whitespace = S(" \t")
local line_ending = P("\n") + P("\r\n") + P("\r")
local whitespace = intraline_whitespace + line_ending
local comment = P(";") * (P(1) - line_ending)^0
local atmosphere = whitespace + comment
local intertoken_space = atmosphere^1

-- Tokens, bottom-up
local vertical_line = P("|")
local backslash = P("\\")
local letter = R("az") + R("AZ")
local digit = R("09")
local hex_digit = digit + R("af") + R("AF")
local explicit_sign = S("+-")
local special_initial = S("!$%&*/:<=>?^_~")
local initial = letter + special_initial
local special_subsequent = explicit_sign + S(".@")
local subsequent = initial + digit + special_subsequent

local mnemonic_mapping = {
	["\\a"] = "\a",
	["\\b"] = "\b",
	["\\t"] = "\t",
	["\\n"] = "\n",
	["\\r"] = "\r",
}

local mnemonic_mapping_rev = {
	["\a"] = "\\a",
	["\b"] = "\\b",
	["\t"] = "\\t",
	["\n"] = "\\n",
	["\r"] = "\\r",
}

local mnemonic_escape =
	P("\\") * S("abtnr")

local hex_scalar_value = hex_digit^1 / function(s) return tonumber(s, 16) end
local inline_hex_escape = P("\\x") * (hex_scalar_value / string.char) * P(";")
local sign_subsequent = initial + explicit_sign + P("@")
local dot_subsequent = sign_subsequent + P(".")

-- Any captures are replacements to the string that was matched
local symbol_element =
	(P(1) - S("|\\"))
	+ Cg(inline_hex_escape)
	+ mnemonic_escape / mnemonic_mapping
	+ Cg(P("\\|") * Cc("|"))

local peculiar_identifier = explicit_sign
	+ explicit_sign * sign_subsequent * subsequent^0
	+ explicit_sign * P(".") * dot_subsequent * subsequent^0
	+ P(".") * dot_subsequent * subsequent^0

-- Captures an identifier string
local identifier_str = C(initial * subsequent^0)
	+ vertical_line * Cs(symbol_element^0) * vertical_line
	+ C(peculiar_identifier)

-- Captures an identifier value
local identifier = identifier_str / val_symbol

-- Captures a boolean value
local boolean = P("#true") * Cc(true)
	+ P("#false") * Cc(false)
	+ P("#t") * Cc(true)
	+ P("#f") * Cc(false)

-- Captures a string
local char_name = P("alarm") * Cc("\a")
	+ P("backspace") * Cc("\b")
	+ P("delete") * Cc("\127")
	+ P("escape") * Cc("\027")
	+ P("newline") * Cc("\n")
	+ P("null") * Cc("\000")
	+ P("return") * Cc("\r")
	+ P("space") * Cc(" ")
	+ P("tab") * Cc("\t")

local char_body = P("\\") * (char_name + C(P(1))) + inline_hex_escape

-- Captures a character value
local char = P("#") * char_body / val_char

-- Any captures are substitutions that should be applied
local string_element = (P(1) - S("\"\\"))
	+ mnemonic_escape / mnemonic_mapping
	+ Cg(P("\\\"") * Cc("\""))
	+ Cg(P("\\\\") * Cc("\\"))
	+ Cg(backslash * intraline_whitespace^0 * line_ending
		* intraline_whitespace^0 * Cc(""))
	+ Cg(inline_hex_escape)

-- Captures a string value
local string_v = P("\"") * Cs(string_element^0) * P("\"")

local function tonumber_b(b)
	return function(s)
		return tonumber(s, b)
	end
end

-- Captures the base
local radix = {
	[2] = P("#b"),
	[8] = P("#o"),
	[10] = (P(true) + P("#d")),
	[16] = P("#x"),
}

local digit_n = {
	[2] = R("01"),
	[8] = R("07"),
	[10] = digit,
	[16] = hex_digit,
}

-- exactness is unused currently
local exactness = P("#i") + P("#e") + P(true)
local sign = P("+") + P("-") + P(true)
local exponent_marker = P("e")
local suffix = exponent_marker * sign * digit_n[10]^1 + P(true)

-- Captures a number
local infnan = P("+inf.0") * Cc(1/0)
	+ P("-inf.0") * Cc(-1/0)
	+ P("+nan.0") * Cc(0/0)
	+ P("-nan.0") * Cc(-0/0)

local function uinteger(r)
	return digit_n[r]^1
end

local function decimal(r)
	if r ~= 10 then
		return P(false)
	end
	
	return P(".") * digit_n[10]^1 * suffix
		+ digit_n[10]^1 * P(".") * digit_n[10]^0 * suffix
		+ uinteger(10) * suffix
end

-- Captures a number
local function uinteger_c(r)
	return uinteger(r) / tonumber_b(r)
end

-- Captures a number
local function urational_c(r)
	return (uinteger_c(r) * P("/") * uinteger_c(r)) / function(m,n)
		return m / n
	end
end

-- Captures a number
local function ureal(r)
	return urational_c(r)
		+ decimal(r) / tonumber -- Always rad 10
		+ uinteger_c(r)
end

-- Captures a number
local function real(r)
	return infnan
		+ (C(sign) * ureal(r)) / function(sgn, num)
			if sgn == "" or sgn == "+" then
				return num
			else
				return -num
			end
	end
end

local function num(r)
	return radix[r] * real(r)
end

local number = num(2) + num(8) + num(10) + num(16)

local token = identifier
	+ boolean
	+ char
	+ number
	+ string_v
	+ P("(") * Cc(tok_lparen)
	+ P(")") * Cc(tok_rparen)
	+ P("#(") * Cc(tok_vecstart)
	+ P("#u8") * Cc(tok_bytevecstart)
	+ P("'") * Cc(tok_quote)
	+ P("`") * Cc(tok_backquote)
	+ P(",@") * Cc(tok_unquote_splice)
	+ P(",") * Cc(tok_unquote)
	+ P(".") * Cc(tok_dot)

local intertoken_w_position = intertoken_space * Cp()
local token_w_position = token * Cp()

local function lex_error(str, start_i)
	local prefix = string.sub(str, start_i, start_i + 10)

	return string.format("%q", prefix)
end

-- On success, returns the current position and the token lexed. On failure,
-- returns nil and a prefix of the bad token. On safely reaching eof, returns -1.
local function lex(str, start_i)
	if start_i > #str then return -1 end

	local new_i = lpeg_match(intertoken_w_position, str, start_i)
	if new_i then
		return lex(str, new_i)
	end

	local token, new_i = lpeg_match(token_w_position, str, start_i)
	if new_i then
		return new_i, token
	end

	-- Lexer failure
	return nil, lex_error(str, start_i)
end

-- *** Parser ***

local quote_symb = val_symbol("quote")
local backquote_symb = val_symbol("quasiquote")
local unquote_symb = val_symbol("unquote")
local unquote_splice_symb = val_symbol("unquote-splice")

-- Pairs of what prefixes the next expression, and what to call it when erroring.
local prefixers = {
	[tok_quote] = { quote_symb, "'" },
	[tok_backquote] = { backquote_symb, "`" },
	[tok_unquote] = { unquote_symb, "," },
	[tok_unquote_splice] = { unquote_splice_symb, ",@" },
}

local parse_exp

-- Can never report eof
local function parse_list(str, start_i)
	local next_i, res = lex(str, start_i)

	if next_i == -1 then
		return nil, "Unclosed parenthesis"
	elseif not next_i then
		return nil, "Bad token near: " .. res
	elseif is_value_tok(res) then
		local next_next_i, tail = parse_list(str, next_i)

		if not next_next_i then 
			return nil, tail
		else
			return next_next_i, val_compair(res, tail)
		end
	elseif res == tok_lparen then
		local next_next_i, head = parse_list(str, next_i)

		if not next_next_i then
			return nil, head
		else
			local next_3_i, tail = parse_list(str, next_next_i)

			if not next_3_i then
				return nil, tail
			else
				return next_3_i, val_compair(head, tail)
			end
		end
	elseif res == tok_rparen then
		return next_i, the_empty
	elseif res == tok_dot then
		-- Next expression will be the tail
		local next_next_i, tail = parse_exp(str, next_i)

		if not next_next_i then
			return nil, "Ill-formed dotted list"
		elseif next_next_i == -1 then
			return nil, "Unclosed parenthesis"
		else
			local next_3_i, next_2_res = lex(str, next_next_i)

			if not next_3_i then
				return nil, "Bad token near: " .. next_2_res
			elseif next_3_i == -1 then
				return nil, "Unclosed parenthesis"
			elseif next_2_res == tok_rparen then
				-- List finished properly
				return next_3_i, tail
			else
				-- Too much stuff after dot
				return nil, "Ill-formed dotted list"
			end
		end
	end

	local prefixer = prefixers[res]

	if prefixer then
		local next_next_i, next_res = parse_exp(str, next_i)
		if not next_next_i then
			return nil, next_res
		elseif next_next_i == -1 then
			return nil, prefixer[2] .. " must prefix an expression."
		else 
			local head = val_compair(prefixer[1],
					val_compair(next_res, the_empty))

			local next_3_i, tail = parse_list(str, next_next_i)

			if not next_3_i then
				return nil, tail
			else
				return next_3_i, val_compair(head, tail)
			end
		end
	end
end

-- Returns next position and exp on success, otherwise returns nil and an error
-- message. On safely reach eof, returns -1.
-- This can produce improper lists, though never infinite ones.
function parse_exp(str, start_i)
	local next_i, res = lex(str, start_i)

	if next_i == -1 then
		return -1
	elseif not next_i then
		return nil, "Bad token near: " .. res
	elseif is_value_tok(res) then
		return next_i, res
	elseif res == tok_lparen then
		return parse_list(str, next_i)
	elseif res == tok_rparen then
		return nil, "Unmatched closing parenthesis"
	elseif res == tok_dot then
		return nil, "Free dot"
	end

	local prefixer = prefixers[res]

	if prefixer then
		local next_next_i, next_res = parse_exp(str, next_i)
		if not next_next_i then
			return nil, next_res
		elseif next_next_i == -1 then
			return nil, prefixer[2] .. " must prefix an expression."
		else
			return next_next_i, val_compair(prefixer[1],
				val_compair(next_res, the_empty))
		end
	end

	if res == tok_vecstart or res == tok_bytevecstart then
		return "(Byte)Vector literals unsupported"
	end
	
	return nil, "Unsupported token"
end

local plus_inf = 1/0
local neg_inf = -1/0

local render_exp

local function render_number(num)
	if num ~= num then -- it is nan
		return "+nan.0"
	elseif num == plus_inf then
		return "+inf.0"
	elseif num == neg_inf then
		return "-inf.0"
	else
		return tostring(num)
	end
end

local function render_boolean(bool)
	if bool then
		return "#t"
	else
		return "#f"
	end
end

-- Second input is a table to add things to. This is for rendering lists as
-- "proper" as possible.
local function render_pair_helper(exp, acctable, idx)
	if type(exp) == "table" then
		if exp.tag == "compair" then
			acctable[idx] = render_exp(exp.car)
			render_pair_helper(exp.cdr, acctable, idx + 1)
		elseif exp ~= the_empty then -- Improper tail
			acctable[idx] = "."
			acctable[idx + 1] = render_exp(exp.cdr)
		end -- else don't need to do anything for empty
	else -- Same as the above case
		acctable[idx] = "."
		acctable[idx + 1] = render_exp(exp)
	end
end

local function render_pair(pair)
	local concat_this = {}
	concat_this[1] = render_exp(pair.car)
	render_pair_helper(pair.cdr, concat_this, 2)

	return "(" .. table.concat(concat_this, " ") .. ")"
end

-- One that can be constructed without |
local ordinary_symbol = (initial * subsequent^0 + peculiar_identifier) * P(-1)

local function escape_char(str)
	if mnemonic_mapping_rev[str] then
		return mnemonic_mapping_rev[str]
	else
		return "\\x" .. string.format("%x", string.byte(str))
	end
end

local function escape_ident_char(str)
	if mnemonic_mapping_rev[str] then
		return mnemonic_mapping_rev[str]
	elseif str == "|" then
		return "\\|"
	else
		return "\\x" .. string.format("%x", string.byte(str))
	end
end

local function escape_ident(str)
	return string.gsub(str, "[%c|]", escape_ident_char)
end

local function render_symbol(symbol)
	local symname = symbol.symbol
	if lpeg.match(ordinary_symbol, symname) then
		return symname
	else
		return "|" .. escape_ident(symname) .. "|"
	end
end

local char_escapes = {
	["\a"] = "alarm",
	["\b"] = "backspace",
	["\127"] = "delete",
	["\027"] = "escape",
	["\n"] = "newline",
	["\000"] = "null",
	["\r"] = "return",
	[" "] = "space",
	["\t"] = "tab",
}

local function render_char(char)
	local char_str = char.char

	if char_escapes[char_str] then
		return "#\\" .. char_escapes[char_str]
	elseif string.find(char_str, "%c") then
		return "#\\x" .. string.format("%x", string.byte(char_str))
	else
		return "#\\" .. char_str
	end
end

local function render_string(str)
	return "\"" .. string.gsub(str, "%c", escape_char) .. "\""
end

local function render_empty(the_empty)
	return "()"
end

function render_exp(exp)
	local e_type = type(exp)

	if e_type == "table" then
		local tag = exp.tag

		if tag == "compair" then
			return render_pair(exp)
		elseif tag == "symbol" then
			return render_symbol(exp)
		elseif tag == "char" then
			return render_char(exp)
		elseif tag == "empty" then
			return render_empty(exp)
		else
			error("Bad expression type: " .. tag)
		end
	elseif e_type == "number" then
		return render_number(exp)
	elseif e_type == "boolean" then
		return render_boolean(exp)
	elseif e_type == "string" then
		return render_string(exp)
	end
end

local function parse_test_loop()
	print("Exp?")
	local input = io.read("*line")

	if input == "***quit***" then return end

	local next_i = 1

	while next_i ~= nil and next_i >= 0 do
		next_i, res = parse_exp(input, next_i)

		if not next_i then
			print("Bad input: " .. res)
		elseif next_i ~= -1 then
			print(render_exp(res))
		end -- Don't do anything if finished
	end

	parse_test_loop()
end



-- Export for debugging
vm.parsers = {}
vm.parsers.number = number * P(-1)
vm.parsers.string = string_v * P(-1)
vm.parsers.symbol = identifier * P(-1)
vm.parsers.char = char * P(-1)
vm.parsers.boolean = boolean * P(-1)
vm.lex = lex
vm.parse_test_loop = parse_test_loop

return vm
