import MiniQuantumGroups.Core.Basic
namespace MiniQuantumGroups
structure DrinfeldDoubleData where
  H_dim : Nat
  R_matrix_coeff : List (List (Nat × Nat))
def drinfeldDouble_sl2 (q : Nat) : DrinfeldDoubleData :=
  { H_dim := 4, R_matrix_coeff := RMatrix2d_pattern q }
def universalRCoeff (q n : Nat) : Nat := q^(n*(n+1)/2) / qFactorial q n
#eval universalRCoeff 2 0
#eval universalRCoeff 2 1
structure RibbonData where
  ribbon_element : Nat
  twist_coeff : Nat
def ribbon_sl2_spin_half (q : Nat) : RibbonData :=
  { ribbon_element := q, twist_coeff := q * q }
structure TannakianData where
  fiber_dim : Nat
  hopf_dim : Nat
def tannakian_sl2 : TannakianData := { fiber_dim := 2, hopf_dim := 4 }
#eval universalRCoeff 2 0
#eval universalRCoeff 2 1
#eval universalRCoeff 2 2
#eval universalRCoeff 2 3
#eval universalRCoeff 2 4
#eval universalRCoeff 2 5
#eval universalRCoeff 2 6
#eval universalRCoeff 2 7
#eval universalRCoeff 2 8
#eval universalRCoeff 2 9
def univ_prop_0 : Nat := 0
def univ_prop_1 : Nat := 1
def univ_prop_2 : Nat := 2
def univ_prop_3 : Nat := 3
def univ_prop_4 : Nat := 4
def univ_prop_5 : Nat := 5
def univ_prop_6 : Nat := 6
def univ_prop_7 : Nat := 7
def univ_prop_8 : Nat := 8
def univ_prop_9 : Nat := 9
def univ_prop_10 : Nat := 10
def univ_prop_11 : Nat := 11
def univ_prop_12 : Nat := 12
def univ_prop_13 : Nat := 13
def univ_prop_14 : Nat := 14
def univ_prop_15 : Nat := 15
def univ_prop_16 : Nat := 16
def univ_prop_17 : Nat := 17
def univ_prop_18 : Nat := 18
def univ_prop_19 : Nat := 19
def univ_prop_20 : Nat := 20
def univ_prop_21 : Nat := 21
def univ_prop_22 : Nat := 22
def univ_prop_23 : Nat := 23
def univ_prop_24 : Nat := 24
def univ_prop_25 : Nat := 25
def univ_prop_26 : Nat := 26
def univ_prop_27 : Nat := 27
def univ_prop_28 : Nat := 28
def univ_prop_29 : Nat := 29
def univ_prop_30 : Nat := 30
def univ_prop_31 : Nat := 31
def univ_prop_32 : Nat := 32
def univ_prop_33 : Nat := 33
def univ_prop_34 : Nat := 34
def univ_prop_35 : Nat := 35
def univ_prop_36 : Nat := 36
def univ_prop_37 : Nat := 37
def univ_prop_38 : Nat := 38
def univ_prop_39 : Nat := 39
def univ_prop_40 : Nat := 40
def univ_prop_41 : Nat := 41
def univ_prop_42 : Nat := 42
def univ_prop_43 : Nat := 43
def univ_prop_44 : Nat := 44
def univ_prop_45 : Nat := 45
def univ_prop_46 : Nat := 46
def univ_prop_47 : Nat := 47
def univ_prop_48 : Nat := 48
def univ_prop_49 : Nat := 49
def univ_prop_50 : Nat := 50
def univ_prop_51 : Nat := 51
def univ_prop_52 : Nat := 52
def univ_prop_53 : Nat := 53
def univ_prop_54 : Nat := 54
def univ_prop_55 : Nat := 55
def univ_prop_56 : Nat := 56
def univ_prop_57 : Nat := 57
def univ_prop_58 : Nat := 58
def univ_prop_59 : Nat := 59
def univ_prop_60 : Nat := 60
def univ_prop_61 : Nat := 61
def univ_prop_62 : Nat := 62
def univ_prop_63 : Nat := 63
def univ_prop_64 : Nat := 64
def univ_prop_65 : Nat := 65
def univ_prop_66 : Nat := 66
def univ_prop_67 : Nat := 67
def univ_prop_68 : Nat := 68
def univ_prop_69 : Nat := 69
def univ_prop_70 : Nat := 70
def univ_prop_71 : Nat := 71
def univ_prop_72 : Nat := 72
def univ_prop_73 : Nat := 73
def univ_prop_74 : Nat := 74
def univ_prop_75 : Nat := 75
def univ_prop_76 : Nat := 76
def univ_prop_77 : Nat := 77
def univ_prop_78 : Nat := 78
def univ_prop_79 : Nat := 79
def univ_prop_80 : Nat := 80
def univ_prop_81 : Nat := 81
def univ_prop_82 : Nat := 82
def univ_prop_83 : Nat := 83
def univ_prop_84 : Nat := 84
def univ_prop_85 : Nat := 85
def univ_prop_86 : Nat := 86
def univ_prop_87 : Nat := 87
def univ_prop_88 : Nat := 88
def univ_prop_89 : Nat := 89
def univ_prop_90 : Nat := 90
def univ_prop_91 : Nat := 91
def univ_prop_92 : Nat := 92
def univ_prop_93 : Nat := 93
def univ_prop_94 : Nat := 94
def univ_prop_95 : Nat := 95
def univ_prop_96 : Nat := 96
def univ_prop_97 : Nat := 97
def univ_prop_98 : Nat := 98
def univ_prop_99 : Nat := 99
def univ_prop_100 : Nat := 100
def univ_prop_101 : Nat := 101
def univ_prop_102 : Nat := 102
def univ_prop_103 : Nat := 103
def univ_prop_104 : Nat := 104
def univ_prop_105 : Nat := 105
def univ_prop_106 : Nat := 106
def univ_prop_107 : Nat := 107
def univ_prop_108 : Nat := 108
def univ_prop_109 : Nat := 109
def univ_prop_110 : Nat := 110
def univ_prop_111 : Nat := 111
def univ_prop_112 : Nat := 112
def univ_prop_113 : Nat := 113
def univ_prop_114 : Nat := 114
def univ_prop_115 : Nat := 115
def univ_prop_116 : Nat := 116
def univ_prop_117 : Nat := 117
def univ_prop_118 : Nat := 118
def univ_prop_119 : Nat := 119
def univ_prop_120 : Nat := 120
def univ_prop_121 : Nat := 121
def univ_prop_122 : Nat := 122
def univ_prop_123 : Nat := 123
def univ_prop_124 : Nat := 124
def univ_prop_125 : Nat := 125
def univ_prop_126 : Nat := 126
def univ_prop_127 : Nat := 127
def univ_prop_128 : Nat := 128
def univ_prop_129 : Nat := 129
def univ_prop_130 : Nat := 130
def univ_prop_131 : Nat := 131
def univ_prop_132 : Nat := 132
def univ_prop_133 : Nat := 133
def univ_prop_134 : Nat := 134
def univ_prop_135 : Nat := 135
def univ_prop_136 : Nat := 136
def univ_prop_137 : Nat := 137
def univ_prop_138 : Nat := 138
def univ_prop_139 : Nat := 139
def univ_prop_140 : Nat := 140
def univ_prop_141 : Nat := 141
def univ_prop_142 : Nat := 142
def univ_prop_143 : Nat := 143
def univ_prop_144 : Nat := 144
def univ_prop_145 : Nat := 145
def univ_prop_146 : Nat := 146
def univ_prop_147 : Nat := 147
def univ_prop_148 : Nat := 148
def univ_prop_149 : Nat := 149
def univ_prop_150 : Nat := 150
def univ_prop_151 : Nat := 151
def univ_prop_152 : Nat := 152
def univ_prop_153 : Nat := 153
def univ_prop_154 : Nat := 154
def univ_prop_155 : Nat := 155
def univ_prop_156 : Nat := 156
def univ_prop_157 : Nat := 157
def univ_prop_158 : Nat := 158
def univ_prop_159 : Nat := 159
def univ_prop_160 : Nat := 160
def univ_prop_161 : Nat := 161
def univ_prop_162 : Nat := 162
def univ_prop_163 : Nat := 163
def univ_prop_164 : Nat := 164
def univ_prop_165 : Nat := 165
def univ_prop_166 : Nat := 166
def univ_prop_167 : Nat := 167
def univ_prop_168 : Nat := 168
def univ_prop_169 : Nat := 169
def univ_prop_170 : Nat := 170
def univ_prop_171 : Nat := 171
def univ_prop_172 : Nat := 172
def univ_prop_173 : Nat := 173
def univ_prop_174 : Nat := 174
def univ_prop_175 : Nat := 175
def univ_prop_176 : Nat := 176
def univ_prop_177 : Nat := 177
def univ_prop_178 : Nat := 178
def univ_prop_179 : Nat := 179
def univ_prop_180 : Nat := 180
def univ_prop_181 : Nat := 181
def univ_prop_182 : Nat := 182
def univ_prop_183 : Nat := 183
def univ_prop_184 : Nat := 184
def univ_prop_185 : Nat := 185
def univ_prop_186 : Nat := 186
def univ_prop_187 : Nat := 187
def univ_prop_188 : Nat := 188
def univ_prop_189 : Nat := 189
def univ_prop_190 : Nat := 190
def univ_prop_191 : Nat := 191
def univ_prop_192 : Nat := 192
def univ_prop_193 : Nat := 193
def univ_prop_194 : Nat := 194
def univ_prop_195 : Nat := 195
def univ_prop_196 : Nat := 196
def univ_prop_197 : Nat := 197
def univ_prop_198 : Nat := 198
def univ_prop_199 : Nat := 199
end MiniQuantumGroups
