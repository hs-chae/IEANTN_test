/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.PackedSieveKernel
import Lean.Data.RArray
import Mathlib.Algebra.BigOperators.Intervals

/-! Exact byte-table population count. Every table entry is proved, and the
generic theorem counts the low 8*k bits. Kernel arithmetic alone is not PV. -/
namespace RamanujanPV.PackedSieveByteCount
open Finset
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def byteTable : Lean.RArray Nat := (.branch 128 (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf 0) (.leaf 1)) (.branch 3 (.leaf 1) (.leaf 2))) (.branch 6 (.branch 5 (.leaf 1) (.leaf 2)) (.branch 7 (.leaf 2) (.leaf 3)))) (.branch 12 (.branch 10 (.branch 9 (.leaf 1) (.leaf 2)) (.branch 11 (.leaf 2) (.leaf 3))) (.branch 14 (.branch 13 (.leaf 2) (.leaf 3)) (.branch 15 (.leaf 3) (.leaf 4))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf 1) (.leaf 2)) (.branch 19 (.leaf 2) (.leaf 3))) (.branch 22 (.branch 21 (.leaf 2) (.leaf 3)) (.branch 23 (.leaf 3) (.leaf 4)))) (.branch 28 (.branch 26 (.branch 25 (.leaf 2) (.leaf 3)) (.branch 27 (.leaf 3) (.leaf 4))) (.branch 30 (.branch 29 (.leaf 3) (.leaf 4)) (.branch 31 (.leaf 4) (.leaf 5)))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf 1) (.leaf 2)) (.branch 35 (.leaf 2) (.leaf 3))) (.branch 38 (.branch 37 (.leaf 2) (.leaf 3)) (.branch 39 (.leaf 3) (.leaf 4)))) (.branch 44 (.branch 42 (.branch 41 (.leaf 2) (.leaf 3)) (.branch 43 (.leaf 3) (.leaf 4))) (.branch 46 (.branch 45 (.leaf 3) (.leaf 4)) (.branch 47 (.leaf 4) (.leaf 5))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf 2) (.leaf 3)) (.branch 51 (.leaf 3) (.leaf 4))) (.branch 54 (.branch 53 (.leaf 3) (.leaf 4)) (.branch 55 (.leaf 4) (.leaf 5)))) (.branch 60 (.branch 58 (.branch 57 (.leaf 3) (.leaf 4)) (.branch 59 (.leaf 4) (.leaf 5))) (.branch 62 (.branch 61 (.leaf 4) (.leaf 5)) (.branch 63 (.leaf 5) (.leaf 6))))))) (.branch 96 (.branch 80 (.branch 72 (.branch 68 (.branch 66 (.branch 65 (.leaf 1) (.leaf 2)) (.branch 67 (.leaf 2) (.leaf 3))) (.branch 70 (.branch 69 (.leaf 2) (.leaf 3)) (.branch 71 (.leaf 3) (.leaf 4)))) (.branch 76 (.branch 74 (.branch 73 (.leaf 2) (.leaf 3)) (.branch 75 (.leaf 3) (.leaf 4))) (.branch 78 (.branch 77 (.leaf 3) (.leaf 4)) (.branch 79 (.leaf 4) (.leaf 5))))) (.branch 88 (.branch 84 (.branch 82 (.branch 81 (.leaf 2) (.leaf 3)) (.branch 83 (.leaf 3) (.leaf 4))) (.branch 86 (.branch 85 (.leaf 3) (.leaf 4)) (.branch 87 (.leaf 4) (.leaf 5)))) (.branch 92 (.branch 90 (.branch 89 (.leaf 3) (.leaf 4)) (.branch 91 (.leaf 4) (.leaf 5))) (.branch 94 (.branch 93 (.leaf 4) (.leaf 5)) (.branch 95 (.leaf 5) (.leaf 6)))))) (.branch 112 (.branch 104 (.branch 100 (.branch 98 (.branch 97 (.leaf 2) (.leaf 3)) (.branch 99 (.leaf 3) (.leaf 4))) (.branch 102 (.branch 101 (.leaf 3) (.leaf 4)) (.branch 103 (.leaf 4) (.leaf 5)))) (.branch 108 (.branch 106 (.branch 105 (.leaf 3) (.leaf 4)) (.branch 107 (.leaf 4) (.leaf 5))) (.branch 110 (.branch 109 (.leaf 4) (.leaf 5)) (.branch 111 (.leaf 5) (.leaf 6))))) (.branch 120 (.branch 116 (.branch 114 (.branch 113 (.leaf 3) (.leaf 4)) (.branch 115 (.leaf 4) (.leaf 5))) (.branch 118 (.branch 117 (.leaf 4) (.leaf 5)) (.branch 119 (.leaf 5) (.leaf 6)))) (.branch 124 (.branch 122 (.branch 121 (.leaf 4) (.leaf 5)) (.branch 123 (.leaf 5) (.leaf 6))) (.branch 126 (.branch 125 (.leaf 5) (.leaf 6)) (.branch 127 (.leaf 6) (.leaf 7)))))))) (.branch 192 (.branch 160 (.branch 144 (.branch 136 (.branch 132 (.branch 130 (.branch 129 (.leaf 1) (.leaf 2)) (.branch 131 (.leaf 2) (.leaf 3))) (.branch 134 (.branch 133 (.leaf 2) (.leaf 3)) (.branch 135 (.leaf 3) (.leaf 4)))) (.branch 140 (.branch 138 (.branch 137 (.leaf 2) (.leaf 3)) (.branch 139 (.leaf 3) (.leaf 4))) (.branch 142 (.branch 141 (.leaf 3) (.leaf 4)) (.branch 143 (.leaf 4) (.leaf 5))))) (.branch 152 (.branch 148 (.branch 146 (.branch 145 (.leaf 2) (.leaf 3)) (.branch 147 (.leaf 3) (.leaf 4))) (.branch 150 (.branch 149 (.leaf 3) (.leaf 4)) (.branch 151 (.leaf 4) (.leaf 5)))) (.branch 156 (.branch 154 (.branch 153 (.leaf 3) (.leaf 4)) (.branch 155 (.leaf 4) (.leaf 5))) (.branch 158 (.branch 157 (.leaf 4) (.leaf 5)) (.branch 159 (.leaf 5) (.leaf 6)))))) (.branch 176 (.branch 168 (.branch 164 (.branch 162 (.branch 161 (.leaf 2) (.leaf 3)) (.branch 163 (.leaf 3) (.leaf 4))) (.branch 166 (.branch 165 (.leaf 3) (.leaf 4)) (.branch 167 (.leaf 4) (.leaf 5)))) (.branch 172 (.branch 170 (.branch 169 (.leaf 3) (.leaf 4)) (.branch 171 (.leaf 4) (.leaf 5))) (.branch 174 (.branch 173 (.leaf 4) (.leaf 5)) (.branch 175 (.leaf 5) (.leaf 6))))) (.branch 184 (.branch 180 (.branch 178 (.branch 177 (.leaf 3) (.leaf 4)) (.branch 179 (.leaf 4) (.leaf 5))) (.branch 182 (.branch 181 (.leaf 4) (.leaf 5)) (.branch 183 (.leaf 5) (.leaf 6)))) (.branch 188 (.branch 186 (.branch 185 (.leaf 4) (.leaf 5)) (.branch 187 (.leaf 5) (.leaf 6))) (.branch 190 (.branch 189 (.leaf 5) (.leaf 6)) (.branch 191 (.leaf 6) (.leaf 7))))))) (.branch 224 (.branch 208 (.branch 200 (.branch 196 (.branch 194 (.branch 193 (.leaf 2) (.leaf 3)) (.branch 195 (.leaf 3) (.leaf 4))) (.branch 198 (.branch 197 (.leaf 3) (.leaf 4)) (.branch 199 (.leaf 4) (.leaf 5)))) (.branch 204 (.branch 202 (.branch 201 (.leaf 3) (.leaf 4)) (.branch 203 (.leaf 4) (.leaf 5))) (.branch 206 (.branch 205 (.leaf 4) (.leaf 5)) (.branch 207 (.leaf 5) (.leaf 6))))) (.branch 216 (.branch 212 (.branch 210 (.branch 209 (.leaf 3) (.leaf 4)) (.branch 211 (.leaf 4) (.leaf 5))) (.branch 214 (.branch 213 (.leaf 4) (.leaf 5)) (.branch 215 (.leaf 5) (.leaf 6)))) (.branch 220 (.branch 218 (.branch 217 (.leaf 4) (.leaf 5)) (.branch 219 (.leaf 5) (.leaf 6))) (.branch 222 (.branch 221 (.leaf 5) (.leaf 6)) (.branch 223 (.leaf 6) (.leaf 7)))))) (.branch 240 (.branch 232 (.branch 228 (.branch 226 (.branch 225 (.leaf 3) (.leaf 4)) (.branch 227 (.leaf 4) (.leaf 5))) (.branch 230 (.branch 229 (.leaf 4) (.leaf 5)) (.branch 231 (.leaf 5) (.leaf 6)))) (.branch 236 (.branch 234 (.branch 233 (.leaf 4) (.leaf 5)) (.branch 235 (.leaf 5) (.leaf 6))) (.branch 238 (.branch 237 (.leaf 5) (.leaf 6)) (.branch 239 (.leaf 6) (.leaf 7))))) (.branch 248 (.branch 244 (.branch 242 (.branch 241 (.leaf 4) (.leaf 5)) (.branch 243 (.leaf 5) (.leaf 6))) (.branch 246 (.branch 245 (.leaf 5) (.leaf 6)) (.branch 247 (.leaf 6) (.leaf 7)))) (.branch 252 (.branch 250 (.branch 249 (.leaf 5) (.leaf 6)) (.branch 251 (.leaf 6) (.leaf 7))) (.branch 254 (.branch 253 (.leaf 6) (.leaf 7)) (.branch 255 (.leaf 7) (.leaf 8)))))))))

def lowCount (width bits : Nat) : Nat :=
  ∑ i ∈ range width, if bits.testBit i then 1 else 0

theorem table_correct (b : Nat) (hb : b < 256) :
    byteTable.get b = lowCount 8 b := by
  interval_cases b <;> decide +kernel

def byteCount : Nat → Nat → Nat
  | 0, _ => 0
  | k+1, bits => byteTable.get (bits % 256) + byteCount k (bits / 256)

theorem low_byte (bits : Nat) : lowCount 8 (bits % 256) = lowCount 8 bits := by
  unfold lowCount
  apply sum_congr rfl
  intro i hi
  have hi8 : i < 8 := mem_range.mp hi
  have hbit : (bits % 256).testBit i = bits.testBit i := by
    simpa [hi8] using (Nat.testBit_mod_two_pow bits 8 i)
  rw [hbit]

theorem byteCount_correct (k bits : Nat) :
    byteCount k bits = lowCount (8*k) bits := by
  induction k generalizing bits with
  | zero => simp [byteCount, lowCount]
  | succ k ih =>
    rw [byteCount, table_correct _ (Nat.mod_lt _ (by decide)), low_byte, ih]
    unfold lowCount
    rw [show 8*(k+1)=8+8*k by omega, sum_range_add]
    congr 1
    apply sum_congr rfl
    intro i _
    congr 1
    simpa [Nat.add_comm] using (Nat.testBit_div_two_pow (x := bits) (i := i) (n := 8))

#print axioms table_correct
#print axioms low_byte
#print axioms byteCount_correct
end RamanujanPV.PackedSieveByteCount

