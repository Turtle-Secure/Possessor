--[[
     Obfuscated by Turtle-Secure
]]

local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 79) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 70) then
					if (Enum <= 34) then
						if (Enum <= 16) then
							if (Enum <= 7) then
								if (Enum <= 3) then
									if (Enum <= 1) then
										if (Enum > 0) then
											VIP = Inst[3];
										else
											Stk[Inst[2]] = Inst[3] ^ Stk[Inst[4]];
										end
									elseif (Enum > 2) then
										local A = Inst[2];
										do
											return Stk[A](Unpack(Stk, A + 1, Inst[3]));
										end
									else
										local A = Inst[2];
										local Cls = {};
										for Idx = 1, #Lupvals do
											local List = Lupvals[Idx];
											for Idz = 0, #List do
												local Upv = List[Idz];
												local NStk = Upv[1];
												local DIP = Upv[2];
												if ((NStk == Stk) and (DIP >= A)) then
													Cls[DIP] = NStk[DIP];
													Upv[1] = Cls;
												end
											end
										end
									end
								elseif (Enum <= 5) then
									if (Enum == 4) then
										Stk[Inst[2]] = Upvalues[Inst[3]];
									else
										for Idx = Inst[2], Inst[3] do
											Stk[Idx] = nil;
										end
									end
								elseif (Enum == 6) then
									local A = Inst[2];
									Stk[A](Stk[A + 1]);
								else
									Upvalues[Inst[3]] = Stk[Inst[2]];
								end
							elseif (Enum <= 11) then
								if (Enum <= 9) then
									if (Enum > 8) then
										Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
									else
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									end
								elseif (Enum == 10) then
									if (Stk[Inst[2]] < Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Inst[3] ~= 0;
								end
							elseif (Enum <= 13) then
								if (Enum > 12) then
									local NewProto = Proto[Inst[3]];
									local NewUvals;
									local Indexes = {};
									NewUvals = Setmetatable({}, {__index=function(_, Key)
										local Val = Indexes[Key];
										return Val[1][Val[2]];
									end,__newindex=function(_, Key, Value)
										local Val = Indexes[Key];
										Val[1][Val[2]] = Value;
									end});
									for Idx = 1, Inst[4] do
										VIP = VIP + 1;
										local Mvm = Instr[VIP];
										if (Mvm[1] == 35) then
											Indexes[Idx - 1] = {Stk,Mvm[3]};
										else
											Indexes[Idx - 1] = {Upvalues,Mvm[3]};
										end
										Lupvals[#Lupvals + 1] = Indexes;
									end
									Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
								else
									Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								end
							elseif (Enum <= 14) then
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 15) then
								Stk[Inst[2]] = -Stk[Inst[3]];
							elseif Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 25) then
							if (Enum <= 20) then
								if (Enum <= 18) then
									if (Enum == 17) then
										Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									elseif not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 19) then
									Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								else
									Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
								end
							elseif (Enum <= 22) then
								if (Enum == 21) then
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Inst[2] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 23) then
								if (Stk[Inst[2]] == Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 24) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								local A = Inst[2];
								do
									return Unpack(Stk, A, A + Inst[3]);
								end
							end
						elseif (Enum <= 29) then
							if (Enum <= 27) then
								if (Enum > 26) then
									Env[Inst[3]] = Stk[Inst[2]];
								else
									Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
								end
							elseif (Enum == 28) then
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							else
								local A = Inst[2];
								local T = Stk[A];
								local B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							end
						elseif (Enum <= 31) then
							if (Enum > 30) then
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							else
								Stk[Inst[2]] = Stk[Inst[3]];
							end
						elseif (Enum <= 32) then
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
						elseif (Enum == 33) then
							local B = Inst[3];
							local K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
						else
							Stk[Inst[2]] = Inst[3] ~= 0;
						end
					elseif (Enum <= 52) then
						if (Enum <= 43) then
							if (Enum <= 38) then
								if (Enum <= 36) then
									if (Enum > 35) then
										Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									else
										Stk[Inst[2]] = Stk[Inst[3]];
									end
								elseif (Enum > 37) then
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Top));
									end
								end
							elseif (Enum <= 40) then
								if (Enum > 39) then
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								else
									local A = Inst[2];
									local Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum <= 41) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							elseif (Enum == 42) then
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
							else
								do
									return;
								end
							end
						elseif (Enum <= 47) then
							if (Enum <= 45) then
								if (Enum == 44) then
									local A = Inst[2];
									Stk[A] = Stk[A]();
								else
									Stk[Inst[2]] = #Stk[Inst[3]];
								end
							elseif (Enum > 46) then
								do
									return Stk[Inst[2]];
								end
							else
								local A = Inst[2];
								local Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 49) then
							if (Enum == 48) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								local A = Inst[2];
								local T = Stk[A];
								for Idx = A + 1, Top do
									Insert(T, Stk[Idx]);
								end
							end
						elseif (Enum <= 50) then
							Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
						elseif (Enum > 51) then
							Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
						else
							Stk[Inst[2]] = Inst[3] * Stk[Inst[4]];
						end
					elseif (Enum <= 61) then
						if (Enum <= 56) then
							if (Enum <= 54) then
								if (Enum > 53) then
									if (Stk[Inst[2]] <= Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 55) then
								local A = Inst[2];
								local T = Stk[A];
								for Idx = A + 1, Inst[3] do
									Insert(T, Stk[Idx]);
								end
							else
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 58) then
							if (Enum == 57) then
								Stk[Inst[2]] = {};
							elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 59) then
							do
								return;
							end
						elseif (Enum > 60) then
							local NewProto = Proto[Inst[3]];
							local NewUvals;
							local Indexes = {};
							NewUvals = Setmetatable({}, {__index=function(_, Key)
								local Val = Indexes[Key];
								return Val[1][Val[2]];
							end,__newindex=function(_, Key, Value)
								local Val = Indexes[Key];
								Val[1][Val[2]] = Value;
							end});
							for Idx = 1, Inst[4] do
								VIP = VIP + 1;
								local Mvm = Instr[VIP];
								if (Mvm[1] == 35) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						elseif (Stk[Inst[2]] < Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 65) then
						if (Enum <= 63) then
							if (Enum > 62) then
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
							else
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Top));
								end
							end
						elseif (Enum == 64) then
							if (Inst[2] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							Top = (A + Varargsz) - 1;
							for Idx = A, Top do
								local VA = Vararg[Idx - A];
								Stk[Idx] = VA;
							end
						end
					elseif (Enum <= 67) then
						if (Enum > 66) then
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
						else
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
						end
					elseif (Enum <= 68) then
						do
							return Stk[Inst[2]]();
						end
					elseif (Enum > 69) then
						local A = Inst[2];
						Stk[A] = Stk[A]();
					elseif (Inst[2] == Stk[Inst[4]]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 106) then
					if (Enum <= 88) then
						if (Enum <= 79) then
							if (Enum <= 74) then
								if (Enum <= 72) then
									if (Enum > 71) then
										local A = Inst[2];
										local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
										Top = (Limit + A) - 1;
										local Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
									elseif (Inst[2] <= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 73) then
									Stk[Inst[2]] = Inst[3];
								else
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum <= 76) then
								if (Enum == 75) then
									Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
								else
									Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
								end
							elseif (Enum <= 77) then
								Stk[Inst[2]] = {};
							elseif (Enum > 78) then
								local A = Inst[2];
								local Cls = {};
								for Idx = 1, #Lupvals do
									local List = Lupvals[Idx];
									for Idz = 0, #List do
										local Upv = List[Idz];
										local NStk = Upv[1];
										local DIP = Upv[2];
										if ((NStk == Stk) and (DIP >= A)) then
											Cls[DIP] = NStk[DIP];
											Upv[1] = Cls;
										end
									end
								end
							else
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 83) then
							if (Enum <= 81) then
								if (Enum > 80) then
									Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
								elseif (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 82) then
								do
									return Stk[Inst[2]];
								end
							else
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							end
						elseif (Enum <= 85) then
							if (Enum == 84) then
								local A = Inst[2];
								local T = Stk[A];
								for Idx = A + 1, Top do
									Insert(T, Stk[Idx]);
								end
							else
								local A = Inst[2];
								local T = Stk[A];
								local B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							end
						elseif (Enum <= 86) then
							if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 87) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						else
							Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
						end
					elseif (Enum <= 97) then
						if (Enum <= 92) then
							if (Enum <= 90) then
								if (Enum == 89) then
									local A = Inst[2];
									local Step = Stk[A + 2];
									local Index = Stk[A] + Step;
									Stk[A] = Index;
									if (Step > 0) then
										if (Index <= Stk[A + 1]) then
											VIP = Inst[3];
											Stk[A + 3] = Index;
										end
									elseif (Index >= Stk[A + 1]) then
										VIP = Inst[3];
										Stk[A + 3] = Index;
									end
								else
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum == 91) then
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							else
								Stk[Inst[2]] = Inst[3] / Inst[4];
							end
						elseif (Enum <= 94) then
							if (Enum > 93) then
								local B = Inst[3];
								local K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
							else
								Env[Inst[3]] = Stk[Inst[2]];
							end
						elseif (Enum <= 95) then
							Stk[Inst[2]] = #Stk[Inst[3]];
						elseif (Enum == 96) then
							local A = Inst[2];
							local Index = Stk[A];
							local Step = Stk[A + 2];
							if (Step > 0) then
								if (Index > Stk[A + 1]) then
									VIP = Inst[3];
								else
									Stk[A + 3] = Index;
								end
							elseif (Index < Stk[A + 1]) then
								VIP = Inst[3];
							else
								Stk[A + 3] = Index;
							end
						else
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						end
					elseif (Enum <= 101) then
						if (Enum <= 99) then
							if (Enum > 98) then
								if (Stk[Inst[2]] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Inst[3] ^ Stk[Inst[4]];
							end
						elseif (Enum == 100) then
							local A = Inst[2];
							local Index = Stk[A];
							local Step = Stk[A + 2];
							if (Step > 0) then
								if (Index > Stk[A + 1]) then
									VIP = Inst[3];
								else
									Stk[A + 3] = Index;
								end
							elseif (Index < Stk[A + 1]) then
								VIP = Inst[3];
							else
								Stk[A + 3] = Index;
							end
						elseif (Stk[Inst[2]] <= Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 103) then
						if (Enum > 102) then
							do
								return Stk[Inst[2]]();
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
						end
					elseif (Enum <= 104) then
						Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
					elseif (Enum > 105) then
						Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 124) then
					if (Enum <= 115) then
						if (Enum <= 110) then
							if (Enum <= 108) then
								if (Enum > 107) then
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								else
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
								end
							elseif (Enum > 109) then
								local A = Inst[2];
								local Step = Stk[A + 2];
								local Index = Stk[A] + Step;
								Stk[A] = Index;
								if (Step > 0) then
									if (Index <= Stk[A + 1]) then
										VIP = Inst[3];
										Stk[A + 3] = Index;
									end
								elseif (Index >= Stk[A + 1]) then
									VIP = Inst[3];
									Stk[A + 3] = Index;
								end
							elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 112) then
							if (Enum == 111) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							elseif Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 113) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						elseif (Enum > 114) then
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						else
							Stk[Inst[2]] = Upvalues[Inst[3]];
						end
					elseif (Enum <= 119) then
						if (Enum <= 117) then
							if (Enum == 116) then
								if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Inst[3] / Inst[4];
							end
						elseif (Enum == 118) then
							if ((Inst[3] == "_ENV") or (Inst[3] == "getfenv")) then
								Stk[Inst[2]] = Env;
							else
								Stk[Inst[2]] = Env[Inst[3]];
							end
						else
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						end
					elseif (Enum <= 121) then
						if (Enum == 120) then
							local A = Inst[2];
							local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 122) then
						Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
					elseif (Enum == 123) then
						local A = Inst[2];
						local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
						local Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					else
						Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
					end
				elseif (Enum <= 133) then
					if (Enum <= 128) then
						if (Enum <= 126) then
							if (Enum == 125) then
								Stk[Inst[2]] = Stk[Inst[3]] / Stk[Inst[4]];
							else
								Stk[Inst[2]] = Inst[3] * Stk[Inst[4]];
							end
						elseif (Enum > 127) then
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
						else
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum <= 130) then
						if (Enum > 129) then
							Stk[Inst[2]] = -Stk[Inst[3]];
						else
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						end
					elseif (Enum <= 131) then
						local A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Top));
					elseif (Enum == 132) then
						Upvalues[Inst[3]] = Stk[Inst[2]];
					else
						local A = Inst[2];
						Top = (A + Varargsz) - 1;
						for Idx = A, Top do
							local VA = Vararg[Idx - A];
							Stk[Idx] = VA;
						end
					end
				elseif (Enum <= 137) then
					if (Enum <= 135) then
						if (Enum == 134) then
							if (Stk[Inst[2]] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
						end
					elseif (Enum == 136) then
						if (Stk[Inst[2]] <= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
					end
				elseif (Enum <= 139) then
					if (Enum == 138) then
						Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
					elseif ((Inst[3] == "_ENV") or (Inst[3] == "getfenv")) then
						Stk[Inst[2]] = Env;
					else
						Stk[Inst[2]] = Env[Inst[3]];
					end
				elseif (Enum <= 140) then
					Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
				elseif (Enum > 141) then
					Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
				else
					local A = Inst[2];
					do
						return Stk[A](Unpack(Stk, A + 1, Inst[3]));
					end
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
VMCall("LOL!1D3O0003053O006269743332026O002O40027O004003043O00626E6F7403043O0062616E642O033O00626F7203043O0062786F7203063O006C736869667403063O0072736869667403073O006172736869667403063O00737472696E6703043O006368617203043O00627974652O033O007375622O033O0062697403053O007461626C6503063O00636F6E63617403063O00696E7365727403083O00746F6E756D62657203043O00677375622O033O0072657003043O006D61746803053O006C6465787003073O0067657466656E76030C3O007365746D6574617461626C6503053O007063612O6C03063O0073656C65637403063O00756E7061636B030A122O004C4F4C213044334F3O30333036334F2O3037333734373236393645363730333034334F2O30363336383631373230333034334F2O303632373937343635324F302O334F2O3037333735363230333035334F2O303632363937343O332O324F302O334F2O3036323639373430333034334F2O30363237383646373230333035334F2O303734363136323643363530333036334F2O3036333646364536333631373430333036334F2O3036393645373336353732373430333035334F2O303644363137343633363830333038334F2O303734364636453735364436323635373230333035334F2O30373036333631324F36432O303234334F2O30312O3241334F3O3031334F2O3032303338354F3O30322O30312O32413O30313O3031334F2O30323033383O30313O30313O30332O30312O32413O30323O3031334F2O30323033383O30323O30323O30342O30312O32413O30333O3035334F3O303630353O30333O30413O30313O30313O302O3443334F3O30413O30312O30312O32413O30333O3036334F2O30323033383O30343O30333O30372O30312O32413O30353O3038334F2O30323033383O30353O30353O30392O30312O32413O30363O3038334F2O30323033383O30363O30363O30413O303631333O3037334F3O30313O3036324F2O303536334F3O3036344F2O303536384F2O303536334F3O302O344F2O303536334F3O3031344F2O303536334F3O3032344F2O303536334F3O3035334F2O30312O32413O30383O3031334F2O30323033383O30383O30383O30422O30312O32413O30393O3043334F2O30312O32413O30413O3044334F3O303631333O30423O30313O30313O3035324F2O303536334F3O3037344F2O303536334F3O3039344F2O303536334F3O3038344F2O303536334F3O3041344F2O303536334F3O3042344F2O3031443O30433O3042344F2O3032433O30433O3031344F2O3032313O3043364F2O303537334F3O3031334F3O3032334F3O3032334F3O3032364F2O30463033463032364F2O303730342O302O3236344F2O3033423O3032354F2O30313231393O30333O3031344F2O3033433O3034354F2O30313231393O30353O3031334F3O30342O323O30332O3032313O3031324F2O3033393O3037364F2O3031443O30383O3032344F2O3033393O30393O3031344F2O3033393O30413O3032344F2O3033393O30423O3033344F2O3033393O30433O302O344F2O3031443O3044364F2O3031443O30453O3036334F2O30323034363O30463O30363O3031324F2O3035383O30433O3046344F2O3034423O3042334F3O302O324F2O3033393O30433O3033344F2O3033393O30443O302O344F2O3031443O30453O3031344F2O3033433O30463O3031344F3O30423O30463O30363O30462O30313031423O30463O30313O3046324F2O3033432O30314O3031344F3O30422O30314O30362O30313O30313031422O30314O30312O30313O30323034362O30313O30314O3031324F2O3035383O30442O303130344F2O3031413O3043364F2O3034423O3041334F3O30322O30323034333O30413O30413O302O324F2O3032443O30393O3041344F2O3035313O3037334F3O30313O303431343O30333O30353O3031324F2O3033393O30333O3035344F2O3031443O30343O3032344F2O3033463O30333O302O344F2O3032313O3033364F2O303537334F3O3031374F3O3034334F3O3032374F2O30342O30333035334F2O3033413235363432423341324F302O334F2O303235363432423032364F2O30463033462O303143334F3O30363133354F3O30313O3031324F2O303237384F2O3033393O30313O3031344F2O3033393O30323O3032344F2O3033393O30333O3032344F2O3033423O3034364F2O3033393O30353O3033344F2O3031443O302O364F2O3034373O30373O3037344F2O3035383O30353O3037344F2O3031363O3034334F3O30312O30323033383O30343O30343O30312O30313231393O30353O3032344F3O30453O30333O30353O30322O30313231393O30343O3033344F2O3035383O30323O302O344F2O3034423O3031334F3O30322O30323635333O30312O3031383O30313O30343O302O3443334F2O3031383O3031324F2O3031443O3031364F2O3033423O3032364F2O3033463O30313O3032344F2O3032313O3031354F3O302O3443334F2O3031423O3031324F2O3033393O30313O302O344F2O3032433O30313O3031344F2O3032313O3031364F2O303537334F3O3031334F3O3031334F2O303136334F3O3032344F2O30463045344644342O3032364F2O30332O342O3032354F2O3043303539342O3032354F2O303544333234313032344F2O3038374336333234313032334F2O303430364539423545343130333035334F2O303730373236393645373430333034334F2O304543353443382O3330333038334F2O30444539383236424435363943323031383032364F2O304630334630333139334F2O30343946453531423239363745343745383532453739313735343342433534412O38423739344645383545412O38423645303730333036334F2O30314432363943333743374535302O3334334F2O303545373032314142373637353236414633443437312O424336463735323641463645343136384246373437303234453837453733323542383731373933434144373136353638413037343738324445383639373432312O4233443646334342413734372O3246453930333034334F2O3043383144314334383032384F3O30333035334F2O303730363136393732373330333044334F2O3043414345334431344241333446434433322O31372O423245424130333036334F2O3031343941424335343739444630333135334F2O30373336393635372O362O354636462O3635463635373236313734364637333734363836353645363537333032354F2O3034303741342O30333136334F2O3041353233393638314146352O3946382O32453837443441382O3544452O39323943314333424534354342443230333037334F2O30424645443443453141314442333630313437334F3O3036344F2O3034353O3031334F3O302O3443334F2O3034353O30312O30313231393O30313O3031334F2O30323034363O30323O30313O30322O30323034363O30313O30323O30332O30313231393O30323O3034334F2O30313231393O30333O3035334F2O30313231393O30343O3036334F3O303632393O30322O30314O30313O30333O302O3443334F2O30314O30312O30312O32413O30353O3037344F2O3033393O3036354F2O30313231393O30373O3038334F2O30313231393O30383O3039344F2O3035383O30363O3038344F2O3035313O3035334F3O30312O30313031423O30353O30413O30343O303632393O30332O3031393O30313O30353O302O3443334F2O3031393O30312O30312O32413O30353O3037344F2O3033393O3036354F2O30313231393O30373O3042334F2O30313231393O30383O3043344F2O3035383O30363O3038344F2O3035313O3035334F3O30312O30312O32413O30353O3037344F2O3033393O3036354F2O30313231393O30373O3044334F2O30313231393O30383O3045344F2O3035383O30363O3038344F2O3035313O3035334F3O30312O30313231393O30353O3046344F2O3034373O30363O3036334F2O30323635333O30352O3033343O30313O30413O302O3443334F2O3033343O30312O30312O32413O30372O303130344F2O3031443O30383O3036344F3O30433O30373O30323O30393O302O3443334F2O3033313O30313O3036324F3O30422O3033313O3031334F3O302O3443334F2O3033313O30312O30312O32413O30433O3037344F2O3033393O3044354F2O30313231393O30452O302O31334F2O30313231393O30462O303132344F3O30453O30443O30463O302O324F2O3031443O30453O3041344F3O30443O30443O30443O3045324F2O3031463O30433O30323O30313O303634383O30372O3032373O30313O30323O302O3443334F2O3032373O30313O302O3443334F2O3033453O30312O30323635333O30352O3032313O30313O30463O302O3443334F2O3032313O30313O303230343O3037354F2O30312O32423O30372O30312O334F2O30312O32413O30372O30312O334F2O30313231393O30382O30312O344F2O3034453O30373O30323O302O324F2O3031443O30363O3037334F2O30313231393O30353O3041334F3O302O3443334F2O3032313O30312O30312O32413O30353O3037344F2O3033393O3036354F2O30313231393O30372O303135334F2O30313231393O30382O303136344F2O3035383O30363O3038344F2O3035313O3035334F3O30313O302O3443334F2O3034363O30312O30323033383O3031334F3O3041324F2O303537334F3O3031334F3O3031334F3O3037334F3O3032384F3O3032364F2O30463033463032374F2O30342O30333034334F2O30364436313734363830333035334F2O303O3643324F3646373230333034334F2O30373337313732373430313O30313342334F2O30313231393O30313O3031344F2O3034373O30323O3032334F2O30313231393O30333O3031334F2O30323635333O30333O30333O30313O30313O302O3443334F3O30333O30312O30323635333O30312O30324O30313O30323O302O3443334F2O30324O30312O30313231393O30343O3031334F2O30323635333O30343O30383O30313O30313O302O3443334F3O30383O30312O30313231393O30353O302O334F2O30312O32413O30363O3034334F2O30323033383O30363O30363O30352O30312O32413O30373O3034334F2O30323033383O30373O30373O3036324F2O3031443O3038364F2O3032443O30373O3038344F2O3034423O3036334F3O30322O30313231393O30373O3032334F3O30342O323O30352O3031453O3031324F3O30373O30393O30323O30383O3036324F3O30392O3031443O3031334F3O302O3443334F2O3031443O3031324F2O30334O30393O30383O3038324F2O3031443O3041364F2O3031443O30423O3038334F3O30342O323O30392O3031443O30312O30323035323O30323O30433O30373O303431343O30392O3031423O30313O303431343O30352O3031343O3031324F2O3032383O30323O3032334F3O302O3443334F3O30383O30312O30323635333O30313O30323O30313O30313O302O3443334F3O30323O30312O30313231393O30343O3031334F2O30323635333O30342O3033323O30313O30313O302O3443334F2O3033323O3031324F2O3033423O3035364F2O3031443O30323O3035334F2O30313231393O30353O3032344F2O3031443O3036354F2O30313231393O30373O3032334F3O30342O323O30352O3033313O30313O304533353O30322O3032453O30313O30383O302O3443334F2O3032453O3031324F2O3033313O3039364F2O3033413O30393O3031344F2O30324O30323O30383O30393O303431343O30352O3032423O30312O30313231393O30343O3032334F2O30323635333O30342O3032333O30313O30323O302O3443334F2O3032333O30312O30313231393O30313O3032334F3O302O3443334F3O30323O30313O302O3443334F2O3032333O30313O302O3443334F3O30323O30313O302O3443334F3O30333O30313O302O3443334F3O30323O3031324F2O303537334F3O3031374F2O30006F4O00397O00125D3O00013O00127F3O00023O001062000100033O001276000200013O00063D00033O000100012O00233O00013O001077000200040003001276000200013O00063D00030001000100022O00233O00014O00237O001077000200050003001276000200013O00063D00030002000100022O00233O00014O00237O001077000200060003001276000200013O00063D00030003000100022O00233O00014O00237O001077000200070003001276000200013O00063D00030004000100022O00238O00233O00013O001077000200080003001276000200013O00063D00030005000100022O00238O00233O00013O001077000200090003001276000200013O00063D00030006000100022O00238O00233O00013O0010770002000A00030012760002000B3O00207100020002000C0012760003000B3O00207100030003000D0012760004000B3O00207100040004000E001276000500013O00061200050030000100010004693O003000010012760005000F3O002071000600050007001276000700103O002071000700070011001276000800103O00207100080008001200063D00090007000100062O00233O00084O00233O00024O00233O00064O00233O00034O00233O00044O00233O00073O001276000A00133O001276000B000B3O002071000B000B000D001276000C000B3O002071000C000C000C001276000D000B3O002071000D000D000E001276000E000B3O002071000E000E0014001276000F000B3O002071000F000F0015001276001000103O002071001000100011001276001100103O002071001100110012001276001200163O002071001200120017001276001300183O00061200130051000100010004693O0051000100021A001300083O001276001400193O0012760015001A3O0012760016001B3O0012760017001C3O00061200170059000100010004693O00590001001276001700103O00207100170017001C001276001800133O00063D001900090001000D2O00233O000E4O00233O000D4O00233O00094O00233O000B4O00233O000A4O00233O000C4O00233O000F4O00233O00124O00233O00104O00233O00164O00233O00174O00233O00114O00233O00144O001E001A00193O00127F001B001D4O001E001C00134O002C001C000100022O0085001D6O0083001A3O00012O002B3O00013O000A3O00013O00026O00F03F01074O000400016O00665O00012O000400015O00206A0001000100012O0024000100014O002F000100024O002B3O00017O000B3O00025O00E06F40026O007040024O00E0FFEF40026O00F040022O00E03OFFEF41026O00F041028O00026O00F03F027O004003043O006D61746803053O00666C2O6F72022B3O00263500010004000100010004693O0004000100207C00023O00022O002F000200023O00263500010008000100030004693O0008000100207C00023O00042O002F000200023O0026350001000C000100050004693O000C000100207C00023O00062O002F000200024O000400026O006600023O00022O000400036O00660001000100032O001E3O00023O00127F000200073O00127F000300083O00127F000400084O0004000500013O00127F000600083O00046400040029000100207C00083O000900207C000900010009001276000A000A3O002071000A000A000B00202A000B3O00092O001F000A00020002001276000B000A3O002071000B000B000B00202A000C000100092O001F000B000200022O001E0001000B4O001E3O000A4O0020000A00080009002635000A0027000100090004693O002700012O002000020002000300103300030009000300046E0004001700012O002F000200024O002B3O00017O000A3O00025O00E06F40026O007040024O00E0FFEF40026O00F040022O00E03OFFEF41028O00026O00F03F027O004003043O006D61746803053O00666C2O6F72022F3O00263500010006000100010004693O0006000100207C00023O00022O002400023O000200201C0002000200012O002F000200023O0026350001000C000100030004693O000C000100207C00023O00042O002400023O000200201C0002000200032O002F000200023O00263500010010000100050004693O0010000100127F000200054O002F000200024O000400026O006600023O00022O000400036O00660001000100032O001E3O00023O00127F000200063O00127F000300073O00127F000400074O0004000500013O00127F000600073O0004640004002D000100207C00083O000800207C000900010008001276000A00093O002071000A000A000A00202A000B3O00082O001F000A00020002001276000B00093O002071000B000B000A00202A000C000100082O001F000B000200022O001E0001000B4O001E3O000A4O0020000A00080009000E160007002B0001000A0004693O002B00012O002000020002000300103300030008000300046E0004001B00012O002F000200024O002B3O00017O00053O00028O00026O00F03F027O004003043O006D61746803053O00666C2O6F72021F4O000400026O006600023O00022O000400036O00660001000100032O001E3O00023O00127F000200013O00127F000300023O00127F000400024O0004000500013O00127F000600023O0004640004001D000100207C00083O000300207C000900010003001276000A00043O002071000A000A000500202A000B3O00032O001F000A00020002001276000B00043O002071000B000B000500202A000C000100032O001F000B000200022O001E0001000B4O001E3O000A4O0020000A00080009002635000A001B000100020004693O001B00012O002000020002000300103300030003000300046E0004000B00012O002F000200024O002B3O00017O00053O0003043O006D6174682O033O00616273028O0003053O00666C2O6F72027O0040021A3O001276000200013O0020710002000200022O001E000300014O001F0002000200022O000400035O00068800030009000100020004693O0009000100127F000200034O002F000200024O0004000200014O00665O000200260A00010014000100030004693O00140001001276000200013O0020710002000200040010620003000500012O008A00033O00032O008D000200034O005200025O0004693O001900010010620002000500012O008A00023O00022O0004000300014O00660002000200032O002F000200024O002B3O00017O00053O0003043O006D6174682O033O00616273028O0003053O00666C2O6F72027O0040021C3O001276000200013O0020710002000200022O001E000300014O001F0002000200022O000400035O00068800030009000100020004693O0009000100127F000200034O002F000200024O0004000200014O00665O0002000E5000030015000100010004693O00150001001276000200013O0020710002000200042O0082000300013O0010620003000500032O008A00033O00032O008D000200034O005200025O0004693O001B00012O0082000200013O0010620002000500022O008A00023O00022O0004000300014O00660002000200032O002F000200024O002B3O00017O00053O0003043O006D6174682O033O00616273028O00027O004003053O00666C2O6F7202273O001276000200013O0020710002000200022O001E000300014O001F0002000200022O000400035O00068800030009000100020004693O0009000100127F000200034O002F000200024O0004000200014O00665O0002000E5000030020000100010004693O0020000100127F000200034O0004000300013O00202A0003000300040006880003001700013O0004693O001700012O0004000300014O000400046O00240004000400010010620004000400042O0024000200030004001276000300013O0020710003000300052O0082000400013O0010620004000400042O008A00043O00042O001F0003000200022O00200003000300022O002F000300023O0004693O002600012O0082000200013O0010620002000400022O008A00023O00022O0004000300014O00660002000200032O002F000200024O002B3O00017O00023O00026O00F03F026O00704002264O003900025O00127F000300014O005F00045O00127F000500013O0004640003002100012O000400076O001E000800024O0004000900014O0004000A00024O0004000B00034O0004000C00044O001E000D6O001E000E00063O00201C000F000600012O006F000C000F4O0058000B3O00022O0004000C00034O0004000D00044O001E000E00014O005F000F00014O0066000F0006000F00104C000F0001000F2O005F001000014O006600100006001000104C00100001001000201C0010001000012O006F000D00104O0048000C6O0058000A3O000200207C000A000A00022O00300009000A4O008300073O000100046E0003000500012O0004000300054O001E000400024O008D000300044O005200036O002B3O00017O00013O0003043O005F454E5600033O0012763O00014O002F3O00024O002B3O00017O00043O00026O00F03F026O00144003023O006C3803073O00CF4216DC51E21C024A3O00127F000300014O0005000400044O000400056O0004000600014O001E00075O00127F000800024O004A0006000800022O0004000700023O00127F000800033O00127F000900044O004A00070009000200063D00083O000100062O00723O00034O00233O00044O00723O00044O00723O00014O00723O00054O00723O00064O004A0005000800022O001E3O00053O00021A000500013O00063D00060002000100032O00723O00034O00238O00233O00033O00063D00070003000100032O00723O00034O00238O00233O00033O00063D00080004000100032O00723O00034O00238O00233O00033O00063D00090005000100032O00233O00084O00233O00054O00723O00073O00063D000A0006000100072O00723O00054O00723O00034O00723O00014O00233O00084O00238O00233O00034O00723O00084O001E000B00083O00063D000C0007000100012O00723O00093O00063D000D0008000100072O00233O00084O00233O00064O00233O00094O00233O000A4O00233O00054O00233O00074O00233O000D3O00063D000E0009000100072O00233O000C4O00723O00094O00723O000A4O00233O000E4O00723O00024O00723O000B4O00723O000C4O001E000F000E4O001E0010000D4O002C0010000100022O003900116O001E001200014O004A000F001200022O008500106O0025000F6O0052000F6O002B3O00013O000A3O00063O00027O0040025O00C05340028O00026O00F03F034O00026O00304001384O000400016O001E00025O00127F000300014O004A00010003000200263500010015000100020004693O0015000100127F000100033O00263500010007000100030004693O000700012O0004000200024O0004000300034O001E00045O00127F000500043O00127F000600044O006F000300064O005800023O00022O0084000200013O00127F000200054O002F000200023O0004693O000700010004693O0037000100127F000100034O0005000200023O00263500010017000100030004693O001700012O0004000300044O0004000400024O001E00055O00127F000600064O006F000400064O005800033O00022O001E000200034O0004000300013O0006700003003400013O0004693O0034000100127F000300034O0005000400043O00263500030028000100040004693O002800012O002F000400023O00263500030025000100030004693O002500012O0004000500054O001E000600024O0004000700014O004A0005000700022O001E000400054O0005000500054O0084000500013O00127F000300043O0004693O002500010004693O003700012O002F000200023O0004693O003700010004693O001700012O002B3O00017O00033O00028O00026O00F03F027O004003253O0006700002001400013O0004693O0014000100127F000300014O0005000400043O00263500030004000100010004693O0004000100206A0005000100020010620005000300052O007D00053O000500206A00060002000200206A0007000100022O002400060006000700201C0006000600020010620006000300062O006600040005000600207C0005000400022O00240005000400052O002F000500023O0004693O000400010004693O0024000100127F000300014O0005000400043O00263500030016000100010004693O0016000100206A0005000100020010620004000300052O00200005000400042O006600053O000500068800040021000100050004693O0021000100127F000500023O00061200050022000100010004693O0022000100127F000500014O002F000500023O0004693O001600012O002B3O00017O00023O00028O00026O00F03F00133O00127F3O00014O0005000100013O0026353O0005000100020004693O000500012O002F000100023O0026353O0002000100010004693O000200012O000400026O0004000300014O0004000400024O0004000500024O004A0002000500022O001E000100024O0004000200023O00201C0002000200022O0084000200023O00127F3O00023O0004693O000200012O002B3O00017O00023O00027O0040026O007040000D4O00048O0004000100014O0004000200024O0004000300023O00201C0003000300012O002E3O000300012O0004000200023O00201C0002000200012O0084000200023O0020140002000100022O0020000200024O002F000200024O002B3O00017O00073O00028O00026O00F03F026O007041026O00F040026O007040026O000840026O001040001D3O00127F3O00014O0005000100043O0026353O000B000100020004693O000B00010020140005000400030020140006000300042O00200005000500060020140006000200052O00200005000500062O00200005000500012O002F000500023O0026353O0002000100010004693O000200012O000400056O0004000600014O0004000700024O0004000800023O00201C0008000800062O002E0005000800082O001E000400084O001E000300074O001E000200064O001E000100054O0004000500023O00201C0005000500072O0084000500023O00127F3O00023O0004693O000200012O002B3O00017O000C3O00026O00F03F026O003440026O00F041026O003540026O003F40026O002O40026O00F0BF028O00025O00FC9F402O033O004E614E025O00F88F40026O003043003E4O00048O002C3O000100022O000400016O002C00010001000200127F000200014O0004000300014O001E000400013O00127F000500013O00127F000600024O004A0003000600020020140003000300032O0020000300034O0004000400014O001E000500013O00127F000600043O00127F000700054O004A0004000700022O0004000500014O001E000600013O00127F000700064O004A0005000700020026350005001A000100010004693O001A000100127F000500073O0006120005001B000100010004693O001B000100127F000500013O0026350004002A000100080004693O002A000100263500030022000100080004693O002200010020140006000500082O002F000600023O0004693O0035000100127F000600083O00263500060023000100080004693O0023000100127F000400013O00127F000200083O0004693O003500010004693O002300010004693O0035000100263500040035000100090004693O0035000100263500030032000100080004693O003200010030750006000100082O008A00060005000600061200060034000100010004693O003400010012760006000A4O008A0006000500062O002F000600024O0004000600024O001E000700053O00206A00080004000B2O004A00060008000200202A00070003000C2O00200007000200072O008A0006000600072O002F000600024O002B3O00017O00053O00028O00027O0040026O00F03F026O000840034O00013E3O00127F000100014O0005000200033O00263500010016000100020004693O001600012O003900046O001E000300043O00127F000400034O005F000500023O00127F000600033O0004640004001500012O000400086O0004000900014O0004000A00024O001E000B00024O001E000C00074O001E000D00074O006F000A000D4O004800096O005800083O00022O002800030007000800046E0004000A000100127F000100043O00263500010028000100010004693O002800012O0005000200023O0006123O0027000100010004693O0027000100127F000400013O0026350004001C000100010004693O001C00012O0004000500034O002C0005000100022O001E3O00053O0026353O0027000100010004693O0027000100127F000500054O002F000500023O0004693O002700010004693O001C000100127F000100033O00263500010036000100030004693O003600012O0004000400024O0004000500044O0004000600054O0004000700054O0020000700073O00206A0007000700032O004A0004000700022O001E000200044O0004000400054O0020000400044O0084000400053O00127F000100023O00263500010002000100040004693O000200012O0004000400064O001E000500034O008D000400054O005200045O0004693O000200012O002B3O00017O00013O0003013O002300094O003900016O008500026O005400013O00012O000400025O00127F000300014O008500046O004800026O005200016O002B3O00017O00073O00026O00F03F028O00027O0040026O000840026O001040026O00F040026O00184000BE4O00398O003900016O003900026O0039000300044O001E00046O001E000500014O0005000600064O001E000700024O00550003000400012O000400046O002C0004000100022O003900055O00127F000600014O001E000700043O00127F000800013O00046400060033000100127F000A00024O0005000B000C3O002635000A002A000100010004693O002A0001002635000B001D000100010004693O001D00012O0004000D00014O002C000D00010002002635000D001B000100020004693O001B00012O0080000C6O0022000C00013O0004693O00280001002635000B0023000100030004693O002300012O0004000D00024O002C000D000100022O001E000C000D3O0004693O00280001002635000B0028000100040004693O002800012O0004000D00034O002C000D000100022O001E000C000D4O002800050009000C0004693O00320001000E45000200120001000A0004693O001200012O0004000D00014O002C000D000100022O001E000B000D4O0005000C000C3O00127F000A00013O0004693O0012000100046E0006001000012O0004000600014O002C00060001000200107700030004000600127F000600014O000400076O002C00070001000200127F000800013O000464000600B2000100127F000A00024O0005000B000B3O002635000A003D000100020004693O003D00012O0004000C00014O002C000C000100022O001E000B000C4O0004000C00044O001E000D000B3O00127F000E00013O00127F000F00014O004A000C000F0002002635000C00B1000100020004693O00B1000100127F000C00024O0005000D000F3O002635000C0059000100040004693O005900012O0004001000044O001E0011000E3O00127F001200043O00127F001300044O004A00100013000200263500100057000100010004693O005700010020710010000F00052O000C001000050010001077000F000500102O00283O0009000F0004693O00B10001002635000C0088000100010004693O008800012O0039001000044O0004001100054O002C0011000100022O0004001200054O002C0012000100022O0005001300144O00550010000400012O001E000F00103O002635000D0071000100020004693O0071000100127F001000023O00263500100066000100020004693O006600012O0004001100054O002C001100010002001077000F000400112O0004001100054O002C001100010002001077000F000500110004693O008700010004693O006600010004693O00870001002635000D0077000100010004693O007700012O000400106O002C001000010002001077000F000400100004693O00870001002635000D007E000100030004693O007E00012O000400106O002C00100001000200206A001000100006001077000F000400100004693O00870001002635000D0087000100040004693O008700012O000400106O002C00100001000200206A001000100006001077000F000400102O0004001000054O002C001000010002001077000F0005001000127F000C00033O002635000C009F000100030004693O009F00012O0004001000044O001E0011000E3O00127F001200013O00127F001300014O004A00100013000200263500100094000100010004693O009400010020710010000F00032O000C001000050010001077000F000300102O0004001000044O001E0011000E3O00127F001200033O00127F001300034O004A0010001300020026350010009E000100010004693O009E00010020710010000F00042O000C001000050010001077000F0004001000127F000C00043O000E450002004B0001000C0004693O004B00012O0004001000044O001E0011000B3O00127F001200033O00127F001300044O004A0010001300022O001E000D00104O0004001000044O001E0011000B3O00127F001200053O00127F001300074O004A0010001300022O001E000E00103O00127F000C00013O0004693O004B00010004693O00B100010004693O003D000100046E0006003B000100127F000600014O000400076O002C00070001000200127F000800013O000464000600BC000100206A000A000900012O0004000B00064O002C000B000100022O00280001000A000B00046E000600B700012O002F000300024O002B3O00017O00043O00028O00026O00F03F027O0040026O000840031A3O00127F000300014O0005000400063O00263500030007000100010004693O0007000100207100043O000200207100053O000300127F000300023O00263500030002000100020004693O0002000100207100063O000400063D00073O0001000C2O00233O00044O00233O00054O00233O00064O00728O00723O00014O00723O00024O00723O00034O00233O00024O00723O00044O00723O00054O00723O00064O00233O00014O002F000700023O0004693O000200012O002B3O00013O00013O006F3O00026O00F03F026O00F0BF03013O0023028O00025O00804640026O003640026O002440026O001040027O0040026O000840026O001C40026O001440026O001840026O002040026O00224003043O002CF0ACCD03063O00A773B5E29B8A03073O00E527F35A7E7FD003073O00A68242873C1B11026O003040026O002A40026O002640026O002840026O002C40026O002E40026O003340026O003140026O00324003073O007B75C77B34415203053O0050242AAE15030A3O00712F397F5919397E4B0803043O001A2E7057025O00805540026O003440026O003540025O00802O40026O003B40026O003840026O00374003073O00861CA27ABBBA5D03083O00D4D943CB142ODF25030A3O0085B2A6D7AD84A6D6BF9503043O00B2DAEDC8026O003940026O003A40026O003E40026O003C40026O003D40026O003F40026O002O40025O00804340026O004240026O004140025O00804140025O00804240026O004340026O004540026O004440025O0080444003043O008990C8E603043O00B0D6D58603073O00F3A8A2D2AD584F03073O003994CDD6B4C836025O00804540026O004640026O005140026O004C40026O004940025O00804740026O004740026O004840025O00804840025O00804A40025O0080494000026O004A40026O004B40025O00804B40026O004F40025O00804D40025O00804C40026O004D40026O004E40025O00804E40025O00405040025O00804F40026O005040025O00805040025O00C05040026O005440025O00805240025O00C05140025O00405140025O00805140026O005240025O00405240025O00405340025O00C05240026O005340025O00805340025O00C05340025O00C05440025O00405440025O00805440026O005540025O00405540025O00405640025O00C05540026O005640025O00805640025O00C0564000B5053O000400016O0004000200014O0004000300024O0004000400033O00127F000500013O00127F000600024O003900076O003900086O008500096O005400083O00012O0004000900043O00127F000A00034O0085000B6O005800093O000200206A0009000900012O0039000A6O0039000B5O00127F000C00044O001E000D00093O00127F000E00013O000464000C002000010006880003001C0001000F0004693O001C00012O00240010000F000300201C0011000F00012O000C0011000800112O00280007001000110004693O001F000100201C0010000F00012O000C0010000800102O0028000B000F001000046E000C001500012O0024000C0009000300201C000C000C00012O0005000D000E3O00127F000F00043O002635000F0029000100040004693O002900012O000C000D00010005002071000E000D000100127F000F00013O000E45000100240001000F0004693O00240001002665000E0086030100050004693O00860301002665000E00F02O0100060004693O00F02O01002665000E00A9000100070004693O00A90001002665000E0064000100080004693O00640001002665000E0046000100010004693O00460001000E500004003E0001000E0004693O003E00010020710010000D00092O000C0010000B00100020710011000D000A2O000C0011000B00110020710012000D00082O00280010001100120004693O00B005010020710010000D00092O000C0010000B00100006700010004400013O0004693O0044000100201C0005000500010004693O00B005010020710005000D000A0004693O00B00501002665000E0050000100090004693O005000010020710010000D00092O0004001100054O001E0012000B4O001E001300104O001E001400064O008D001100144O005200115O0004693O00B00501002635000E005B0001000A0004693O005B00010020710010000D00092O000C0010000B00100020710011000D000800066D00100059000100110004693O0059000100201C0005000500010004693O00B005010020710005000D000A0004693O00B005010020710010000D00092O0004001100063O0020710012000D000A2O000C0012000200122O0005001300134O0004001400074O004A0011001400022O0028000B001000110004693O00B00501002665000E00810001000B0004693O00810001002665000E00700001000C0004693O007000010020710010000D00092O000C0010000B00100006120010006E000100010004693O006E000100201C0005000500010004693O00B005010020710005000D000A0004693O00B00501002635000E00790001000D0004693O007900010020710010000D00090020710011000D000A2O000C0011000B00110020710012000D00082O000C0011001100122O0028000B001000110004693O00B005010020710010000D00090020710011000D000A2O000C0011000B00110020710012000D00082O000C0012000B00122O000C0011001100122O0028000B001000110004693O00B00501002665000E008B0001000E0004693O008B00010020710010000D00090020710011000D000A00263500110088000100040004693O008800012O008000116O0022001100014O0028000B001000110004693O00B00501000E50000F00910001000E0004693O009100010020710010000D00090020710011000D000A2O0028000B001000110004693O00B005010020710010000D000A2O0004001100083O00127F001200103O00127F001300114O004A0011001300020006560010009F000100110004693O009F00010020710010000D000A2O0004001100083O00127F001200123O00127F001300134O004A00110013000200066D001000A3000100110004693O00A300010020710010000D00092O0004001100074O0028000B001000110004693O00B005010020710010000D00092O0004001100073O0020710012000D000A2O000C0011001100122O0028000B001000110004693O00B00501002665000E000D2O0100140004693O000D2O01002665000E00E6000100150004693O00E60001002665000E00B7000100160004693O00B700010020710010000D00090020710011000D000A2O000C0011000B00110020710012000D00082O000C0012000B00122O00660011001100122O0028000B001000110004693O00B00501000E50001700CF0001000E0004693O00CF000100127F001000044O0005001100123O000E45000400C0000100100004693O00C000010020710011000D000A2O000C0012000B001100127F001000013O002635001000BB000100010004693O00BB000100201C0013001100010020710014000D000800127F001500013O000464001300CA00012O001E001700124O000C0018000B00162O002100120017001800046E001300C600010020710013000D00092O0028000B001300120004693O00B005010004693O00BB00010004693O00B005010020710010000D00092O003900116O000C0012000B001000201C00130010000100201C0013001300042O000C0013000B00132O0030001200134O005400113O000100127F001200044O001E001300103O0020710014000D000800127F001500013O000464001300E5000100127F001700043O000E45000400DD000100170004693O00DD000100201C0012001200012O000C0018001100122O0028000B001600180004693O00E400010004693O00DD000100046E001300DC00010004693O00B00501002665000E00F2000100180004693O00F200010020710010000D00092O000C0011000B00102O0004001200054O001E0013000B3O00201C0014001000010020710015000D000A2O006F001200154O005800113O00022O0028000B001000110004693O00B00501002635000E00F8000100190004693O00F800010020710010000D00092O000C0010000B00102O002F001000023O0004693O00B0050100127F001000044O0005001100123O000E45000100062O0100100004693O00062O0100201C0013001100012O001E001400063O00127F001500013O000464001300052O012O0004001700094O001E001800124O000C0019000B00162O001900170019000100046E00132O002O010004693O00B00501002635001000FA000100040004693O00FA00010020710011000D00092O000C0012000B001100127F001000013O0004693O00FA00010004693O00B00501002665000E00942O01001A0004693O00942O01002665000E00302O01001B0004693O00302O010020710010000D00090020710011000D000800201C0012001000092O003900136O000C0014000B001000201C0015001000012O000C0015000B00152O000C0016000B00122O006F001400164O005400133O000100127F001400014O001E001500113O00127F001600013O000464001400232O012O00200018001200172O000C0019001300172O0028000B0018001900046E0014001F2O010020710014001300010006700014002E2O013O0004693O002E2O0100127F001500043O000E45000400272O0100150004693O00272O012O0028000B001200140020710005000D000A0004693O00B005010004693O00272O010004693O00B0050100201C0005000500010004693O00B00501000E50001C00792O01000E0004693O00792O0100127F001000044O0005001100133O0026350010003A2O0100040004693O003A2O010020710014000D000A2O000C0011000200142O0005001200123O00127F001000013O002635001000522O0100010004693O00522O012O003900146O001E001300144O00040014000A4O003900156O003900163O00022O0004001700083O00127F0018001D3O00127F0019001E4O004A00170019000200063D00183O000100012O00233O00134O00280016001700182O0004001700083O00127F0018001F3O00127F001900204O004A00170019000200063D00180001000100012O00233O00134O00280016001700182O004A0014001600022O001E001200143O00127F001000093O002635001000342O0100090004693O00342O0100127F001400013O0020710015000D000800127F001600013O0004640014006E2O0100201C0005000500012O000C001800010005002071001900180001002635001900642O0100210004693O00642O0100206A0019001700012O0039001A00024O001E001B000B3O002071001C0018000A2O0055001A000200012O002800130019001A0004693O006A2O0100206A0019001700012O0039001A00024O0004001B000B3O002071001C0018000A2O0055001A000200012O002800130019001A2O005F0019000A3O00201C0019001900012O0028000A0019001300046E001400582O010020710014000D00092O0004001500064O001E001600114O001E001700124O0004001800074O004A0015001800022O0028000B001400150004693O00772O010004693O00342O012O004F00105O0004693O00B005010020710010000D00092O001E001100044O000C0012000B00102O0004001300054O001E0014000B3O00201C0015001000012O001E001600064O006F001300164O004800126O007800113O00122O002000130012001000206A00060013000100127F001300044O001E001400104O001E001500063O00127F001600013O000464001400932O0100127F001800043O0026350018008B2O0100040004693O008B2O0100201C0013001300012O000C0019001100132O0028000B001700190004693O00922O010004693O008B2O0100046E0014008A2O010004693O00B00501002665000E00B82O0100220004693O00B82O010020710010000D000900201C0011001000092O000C0011000B00112O000C0012000B00102O00200012001200112O0028000B00100012000E50000400AB2O0100110004693O00AB2O0100201C0013001000012O000C0013000B0013000688001200B0050100130004693O00B0050100127F001300043O002635001300A32O0100040004693O00A32O010020710005000D000A00201C00140010000A2O0028000B001400120004693O00B005010004693O00A32O010004693O00B0050100201C0013001000012O000C0013000B0013000688001300B0050100120004693O00B0050100127F001300043O002635001300B02O0100040004693O00B02O010020710005000D000A00201C00140010000A2O0028000B001400120004693O00B005010004693O00B02O010004693O00B00501000E50002300CF2O01000E0004693O00CF2O0100127F001000044O0005001100123O000E45000100C82O0100100004693O00C82O0100201C0013001100012O001E001400063O00127F001500013O000464001300C72O012O0004001700094O001E001800124O000C0019000B00162O001900170019000100046E001300C22O010004693O00B00501002635001000BC2O0100040004693O00BC2O010020710011000D00092O000C0012000B001100127F001000013O0004693O00BC2O010004693O00B0050100127F001000044O0005001100133O002635001000E92O0100010004693O00E92O0100201C0014001100092O000C0013000B0014000E50000400E02O0100130004693O00E02O0100201C0014001100012O000C0014000B001400063A001400DD2O0100120004693O00DD2O010020710005000D000A0004693O00B0050100201C00140011000A2O0028000B001400120004693O00B0050100201C0014001100012O000C0014000B001400063A001200E62O0100140004693O00E62O010020710005000D000A0004693O00B0050100201C00140011000A2O0028000B001400120004693O00B00501002635001000D12O0100040004693O00D12O010020710011000D00092O000C0012000B001100127F001000013O0004693O00D12O010004693O00B00501002665000E00CB020100240004693O00CB0201002665000E0076020100250004693O00760201002665000E004C020100260004693O004C0201000E50002700050201000E0004693O000502010020710010000D000A2O000C0011000B001000201C0012001000010020710013000D000800127F001400013O0004640012002O02012O001E001600114O000C0017000B00152O002100110016001700046E001200FE2O010020710012000D00092O0028000B001200110004693O00B0050100127F001000044O0005001100133O0026350010000D020100040004693O000D02010020710014000D000A2O000C0011000200142O0005001200123O00127F001000013O00263500100025020100010004693O002502012O003900146O001E001300144O00040014000A4O003900156O003900163O00022O0004001700083O00127F001800283O00127F001900294O004A00170019000200063D00180002000100012O00233O00134O00280016001700182O0004001700083O00127F0018002A3O00127F0019002B4O004A00170019000200063D00180003000100012O00233O00134O00280016001700182O004A0014001600022O001E001200143O00127F001000093O00263500100007020100090004693O0007020100127F001400013O0020710015000D000800127F001600013O00046400140041020100201C0005000500012O000C00180001000500207100190018000100263500190037020100210004693O0037020100206A0019001700012O0039001A00024O001E001B000B3O002071001C0018000A2O0055001A000200012O002800130019001A0004693O003D020100206A0019001700012O0039001A00024O0004001B000B3O002071001C0018000A2O0055001A000200012O002800130019001A2O005F0019000A3O00201C0019001900012O0028000A0019001300046E0014002B02010020710014000D00092O0004001500064O001E001600114O001E001700124O0004001800074O004A0015001800022O0028000B001400150004693O004A02010004693O000702012O004F00105O0004693O00B00501002665000E00520201002C0004693O005202010020710010000D00090020710011000D000A2O0028000B001000110004693O00B00501000E50002D005B0201000E0004693O005B02010020710010000D00090020710011000D000A0020710012000D00082O000C0012000B00122O00200011001100122O0028000B001000110004693O00B005010020710010000D00092O001E001100044O000C0012000B00102O0004001300054O001E0014000B3O00201C0015001000012O001E001600064O006F001300164O004800126O007800113O00122O002000130012001000206A00060013000100127F001300044O001E001400104O001E001500063O00127F001600013O00046400140075020100127F001800043O0026350018006D020100040004693O006D020100201C0013001300012O000C0019001100132O0028000B001700190004693O007402010004693O006D020100046E0014006C02010004693O00B00501002665000E00A50201002E0004693O00A50201002665000E00950201002F0004693O0095020100127F001000044O0005001100133O00263500100087020100040004693O008702010020710011000D00092O003900146O000C0015000B001100201C0016001100012O000C0016000B00162O0030001500164O005400143O00012O001E001200143O00127F001000013O0026350010007C020100010004693O007C020100127F001300044O001E001400113O0020710015000D000800127F001600013O00046400140092020100201C0013001300012O000C0018001200132O0028000B0017001800046E0014008E02010004693O00B005010004693O007C02010004693O00B00501000E50003000A00201000E0004693O00A002010020710010000D00090020710011000D00082O000C0011000B001100066D0010009E020100110004693O009E020100201C0005000500010004693O00B005010020710005000D000A0004693O00B005010020710010000D00090020710011000D000A2O000C0011000B00112O0028000B001000110004693O00B00501002665000E00B3020100310004693O00B3020100127F001000044O0005001100113O002635001000A9020100040004693O00A902010020710011000D00092O000C0012000B001100201C0013001100012O000C0013000B00132O00060012000200010004693O00B005010004693O00A902010004693O00B00501002635000E00BD020100320004693O00BD02010020710010000D00092O000C0010000B00100020710011000D000A2O000C0011000B00110020710012000D00082O000C0012000B00122O00280010001100120004693O00B0050100127F001000044O0005001100113O002635001000BF020100040004693O00BF02010020710011000D00092O0004001200054O001E0013000B4O001E001400114O001E001500064O008D001200154O005200125O0004693O00B005010004693O00BF02010004693O00B00501002665000E0033030100330004693O00330301002665000E00F5020100340004693O00F50201002665000E00E9020100350004693O00E902010020710010000D00092O000C0011000B001000201C0012001000092O000C0012000B0012000E50000400E0020100120004693O00E0020100201C0013001000012O000C0013000B001300063A001300DD020100110004693O00DD02010020710005000D000A0004693O00B0050100201C00130010000A2O0028000B001300110004693O00B0050100201C0013001000012O000C0013000B001300063A001100E6020100130004693O00E602010020710005000D000A0004693O00B0050100201C00130010000A2O0028000B001300110004693O00B00501002635000E00F3020100360004693O00F302010020710010000D00092O000C0010000B0010000612001000F1020100010004693O00F1020100201C0005000500010004693O00B005010020710005000D000A0004693O00B005012O002B3O00013O0004693O00B00501002665000E0025030100370004693O0025030100127F001000044O0005001100133O002635001000FF020100010004693O00FF02012O000C0014000B00112O00200013001400122O0028000B0011001300127F001000093O00263500100005030100040004693O000503010020710011000D000900201C0014001100092O000C0012000B001400127F001000013O002635001000F9020100090004693O00F90201000E5000040016030100120004693O0016030100201C0014001100012O000C0014000B0014000688001300B0050100140004693O00B0050100127F001400043O0026350014000E030100040004693O000E03010020710005000D000A00201C00150011000A2O0028000B001500130004693O00B005010004693O000E03010004693O00B0050100201C0014001100012O000C0014000B0014000688001400B0050100130004693O00B0050100127F001400043O000E450004001B030100140004693O001B03010020710005000D000A00201C00150011000A2O0028000B001500130004693O00B005010004693O001B03010004693O00B005010004693O00F902010004693O00B00501002635000E002D030100380004693O002D03012O0004001000073O0020710011000D000A0020710012000D00092O000C0012000B00122O00280010001100120004693O00B005010020710010000D00092O00040011000B3O0020710012000D000A2O000C0011001100122O0028000B001000110004693O00B00501002665000E005F030100390004693O005F0301002665000E003B0301003A0004693O003B03010020710010000D00092O000C0010000B00102O002F001000023O0004693O00B00501002635000E00470301003B0004693O004703010020710010000D00092O000C0010000B00100020710011000D00082O000C0011000B001100063A00100045030100110004693O0045030100201C0005000500010004693O00B005010020710005000D000A0004693O00B005010020710010000D000A2O0004001100083O00127F0012003C3O00127F0013003D4O004A00110013000200065600100055030100110004693O005503010020710010000D000A2O0004001100083O00127F0012003E3O00127F0013003F4O004A00110013000200066D00100059030100110004693O005903010020710010000D00092O0004001100074O0028000B001000110004693O00B005010020710010000D00092O0004001100073O0020710012000D000A2O000C0011001100122O0028000B001000110004693O00B00501002665000E0067030100400004693O006703012O0004001000073O0020710011000D000A0020710012000D00092O000C0012000B00122O00280010001100120004693O00B00501002635000E006E030100410004693O006E03010020710010000D00092O000C0010000B00102O0067001000014O005200105O0004693O00B005010020710010000D00092O001E001100044O000C0012000B001000201C0013001000012O000C0013000B00132O0030001200134O007800113O00122O002000130012001000206A00060013000100127F001300044O001E001400104O001E001500063O00127F001600013O00046400140085030100127F001800043O0026350018007D030100040004693O007D030100201C0013001300012O000C0019001100132O0028000B001700190004693O008403010004693O007D030100046E0014007C03010004693O00B00501002665000E007C040100420004693O007C0401002665000E0005040100430004693O00050401002665000E00C2030100440004693O00C20301002665000E00A2030100450004693O00A20301000E50004600980301000E0004693O009803010020710010000D00090020710011000D000A2O000C0011000B00110020710012000D00082O000C0012000B00122O008A0011001100122O0028000B001000110004693O00B005010020710010000D00092O000C0011000B00102O0004001200054O001E0013000B3O00201C0014001000012O001E001500064O006F001200154O005800113O00022O0028000B001000110004693O00B00501002665000E00AC030100470004693O00AC03010020710010000D00090020710011000D000A2O000C0011000B00110020710012000D00082O000C0012000B00122O008A0011001100122O0028000B001000110004693O00B00501002635000E00BC030100480004693O00BC030100127F001000043O000E45000400AF030100100004693O00AF03010020710011000D00090020710012000D000A002635001200B6030100040004693O00B603012O008000126O0022001200014O0028000B0011001200201C0005000500010004693O00B005010004693O00AF03010004693O00B005010020710010000D00090020710011000D000A2O000C0011000B00112O005F001100114O0028000B001000110004693O00B00501002665000E00E0030100490004693O00E00301002665000E00CD0301004A0004693O00CD03010020710010000D00090020710011000D000A00127F001200013O000464001000CC030100208C000B0013004B00046E001000CA03010004693O00B00501000E50004C00D80301000E0004693O00D803010020710010000D00090020710011000D00082O000C0011000B001100066D001000D6030100110004693O00D6030100201C0005000500010004693O00B005010020710005000D000A0004693O00B005010020710010000D00092O000C0010000B00100020710011000D000A2O000C0011000B00110020710012000D00082O000C0012000B00122O00280010001100120004693O00B00501002665000E00F80301004D0004693O00F803010020710010000D00092O001E001100044O000C0012000B00102O0004001300054O001E0014000B3O00201C0015001000010020710016000D000A2O006F001300164O004800126O007800113O00122O002000130012001000206A00060013000100127F001300044O001E001400104O001E001500063O00127F001600013O000464001400F7030100201C0013001300012O000C0018001100132O0028000B0017001800046E001400F303010004693O00B00501000E50004E00010401000E0004693O000104010020710010000D00090020710011000D000A2O000C0011000B00110020710012000D00082O000C0011001100122O0028000B001000110004693O00B005010020710010000D00092O003900116O0028000B001000110004693O00B00501002665000E00360401004F0004693O00360401002665000E001F040100500004693O001F0401002665000E0011040100510004693O001104010020710010000D00092O00040011000B3O0020710012000D000A2O000C0011001100122O0028000B001000110004693O00B00501000E50005200170401000E0004693O001704010020710010000D00092O003900116O0028000B001000110004693O00B005010020710010000D00090020710011000D000A0026350011001C040100040004693O001C04012O008000116O0022001100014O0028000B001000110004693O00B00501002665000E0027040100530004693O002704010020710010000D00090020710011000D000A2O000C0011000B00112O005F001100114O0028000B001000110004693O00B00501002635000E0031040100540004693O003104010020710010000D00092O000C0010000B00100006700010002F04013O0004693O002F040100201C0005000500010004693O00B005010020710005000D000A0004693O00B005010020710010000D00092O000C0010000B00102O0067001000014O005200105O0004693O00B00501002665000E005F040100550004693O005F0401002665000E004A040100560004693O004A040100127F001000044O0005001100113O0026350010003C040100040004693O003C04010020710011000D00092O000C0012000B00112O0004001300054O001E0014000B3O00201C0015001100010020710016000D000A2O006F001300164O002500126O005200125O0004693O00B005010004693O003C04010004693O00B00501002635000E0055040100570004693O005504010020710010000D00092O0004001100063O0020710012000D000A2O000C0012000200122O0005001300134O0004001400074O004A0011001400022O0028000B001000110004693O00B005010020710010000D00092O000C0011000B00102O0004001200054O001E0013000B3O00201C0014001000010020710015000D000A2O006F001200154O002500116O005200115O0004693O00B00501002665000E0069040100580004693O006904010020710010000D00090020710011000D000A2O000C0011000B00110020710012000D00082O000C0012000B00122O00660011001100122O0028000B001000110004693O00B00501000E50005900750401000E0004693O007504010020710010000D00092O000C0010000B00100020710011000D00082O000C0011000B001100063A00100073040100110004693O0073040100201C0005000500010004693O00B005010020710005000D000A0004693O00B005010020710010000D00090020710011000D000A2O000C0011000B00110020710012000D00082O00660011001100122O0028000B001000110004693O00B00501002665000E00350501005A0004693O00350501002665000E00EA0401005B0004693O00EA0401002665000E00AC0401005C0004693O00AC0401002665000E009C0401005D0004693O009C04010020710010000D00092O001E001100044O000C0012000B001000201C0013001000012O000C0013000B00132O0030001200134O007800113O00122O002000130012001000206A00060013000100127F001300044O001E001400104O001E001500063O00127F001600013O0004640014009B040100127F001800043O00263500180093040100040004693O0093040100201C0013001300012O000C0019001100132O0028000B001700190004693O009A04010004693O0093040100046E0014009204010004693O00B00501002635000E00A50401005E0004693O00A504010020710010000D00090020710011000D000A2O000C0011000B00110020710012000D00082O00200011001100122O0028000B001000110004693O00B005010020710010000D00090020710011000D000A00127F001200013O000464001000AB040100208C000B0013004B00046E001000A904010004693O00B00501002665000E00CD0401005F0004693O00CD04010020710010000D00090020710011000D000800201C0012001000092O003900136O000C0014000B001000201C0015001000012O000C0015000B00152O000C0016000B00122O006F001400164O005400133O000100127F001400014O001E001500113O00127F001600013O000464001400C004012O00200018001200172O000C0019001300172O0028000B0018001900046E001400BC0401002071001400130001000670001400CB04013O0004693O00CB040100127F001500043O000E45000400C4040100150004693O00C404012O0028000B001200140020710005000D000A0004693O00B005010004693O00C404010004693O00B0050100201C0005000500010004693O00B00501002635000E00DB040100600004693O00DB040100127F001000044O0005001100113O002635001000D1040100040004693O00D104010020710011000D00092O000C0012000B001100201C0013001100012O000C0013000B00132O00060012000200010004693O00B005010004693O00D104010004693O00B0050100127F001000044O0005001100113O002635001000DD040100040004693O00DD04010020710011000D00092O0004001200054O001E0013000B4O001E001400113O0020710015000D000A2O00200015001100152O008D001200154O005200125O0004693O00B005010004693O00DD04010004693O00B00501002665000E0009050100610004693O00090501002665000E00FE040100620004693O00FE040100127F001000044O0005001100113O002635001000F0040100040004693O00F004010020710011000D00092O000C0012000B00112O0004001300054O001E0014000B3O00201C0015001100012O001E001600064O006F001300164O005800123O00022O0028000B001100120004693O00B005010004693O00F004010004693O00B00501000E50006300070501000E0004693O000705010020710010000D00090020710011000D000A0020710012000D00082O000C0012000B00122O00200011001100122O0028000B001000110004693O00B005010020710005000D000A0004693O00B00501002665000E0018050100640004693O0018050100127F001000044O0005001100113O0026350010000D050100040004693O000D05010020710011000D00092O000C0012000B001100201C0013001100012O000C0013000B00132O001F0012000200022O0028000B001100120004693O00B005010004693O000D05010004693O00B00501000E50006500270501000E0004693O0027050100127F001000044O0005001100113O0026350010001C050100040004693O001C05010020710011000D00092O000C0012000B001100201C0013001100012O000C0013000B00132O001F0012000200022O0028000B001100120004693O00B005010004693O001C05010004693O00B0050100127F001000043O00263500100028050100040004693O002805010020710011000D00090020710012000D000A0026350012002F050100040004693O002F05012O008000126O0022001200014O0028000B0011001200201C0005000500010004693O00B005010004693O002805010004693O00B00501002665000E0070050100210004693O00700501002665000E0056050100660004693O00560501002665000E0044050100670004693O004405010020710010000D00092O000C0011000B00102O0004001200054O001E0013000B3O00201C0014001000012O001E001500064O006F001200154O008300113O00010004693O00B00501002635000E004D050100680004693O004D05010020710010000D00092O000C0010000B00100020710011000D000A2O000C0011000B00110020710012000D00082O00280010001100120004693O00B005010020710010000D00092O000C0010000B00100020710011000D000800066D00100054050100110004693O0054050100201C0005000500010004693O00B005010020710005000D000A0004693O00B00501002665000E0062050100690004693O006205010020710010000D00092O000C0011000B00102O0004001200054O001E0013000B3O00201C0014001000010020710015000D000A2O006F001200154O005800113O00022O0028000B001000110004693O00B00501000E50006A00690501000E0004693O006905010020710010000D00090020710011000D000A2O000C0011000B00112O0028000B001000110004693O00B005010020710010000D00090020710011000D000A2O000C0011000B00110020710012000D00082O00200011001100122O0028000B001000110004693O00B00501002665000E009A0501006B0004693O009A0501002665000E00760501006C0004693O007605012O002B3O00013O0004693O00B00501000E50006D007F0501000E0004693O007F05010020710010000D00090020710011000D000A2O000C0011000B00110020710012000D00082O00660011001100122O0028000B001000110004693O00B005010020710010000D00092O001E001100044O000C0012000B00102O0004001300054O001E0014000B3O00201C0015001000010020710016000D000A2O006F001300164O004800126O007800113O00122O002000130012001000206A00060013000100127F001300044O001E001400104O001E001500063O00127F001600013O00046400140099050100127F001800043O00263500180091050100040004693O0091050100201C0013001300012O000C0019001100132O0028000B001700190004693O009805010004693O0091050100046E0014009005010004693O00B00501002665000E009E0501006E0004693O009E05010020710005000D000A0004693O00B00501002635000E00A80501006F0004693O00A805010020710010000D00090020710011000D000A2O000C0011000B00110020710012000D00082O000C0012000B00122O000C0011001100122O0028000B001000110004693O00B005010020710010000D00092O000C0011000B00102O0004001200054O001E0013000B3O00201C0014001000012O001E001500064O006F001200154O008300113O000100201C0005000500010004693O002300010004693O002400010004693O002300012O002B3O00013O00043O00023O00026O00F03F027O004002074O000400026O000C0002000200010020710003000200010020710004000200022O000C0003000300042O002F000300024O002B3O00017O00033O00028O00026O00F03F027O0040030C3O00127F000300014O0005000400043O00263500030002000100010004693O000200012O000400056O000C0004000500010020710005000400020020710006000400032O00280005000600020004693O000B00010004693O000200012O002B3O00017O00033O00028O00026O00F03F027O0040020C3O00127F000200014O0005000300033O00263500020002000100010004693O000200012O000400046O000C0003000400010020710004000300020020710005000300032O000C0004000400052O002F000400023O0004693O000200012O002B3O00017O00033O00028O00026O00F03F027O0040030C3O00127F000300014O0005000400043O000E4500010002000100030004693O000200012O000400056O000C0004000500010020710005000400020020710006000400032O00280005000600020004693O000B00010004693O000200012O002B3O00017O00", GetFEnv(), ...);
