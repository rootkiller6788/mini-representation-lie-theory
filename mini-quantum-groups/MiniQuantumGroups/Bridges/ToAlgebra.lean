/-
MiniQuantumGroups.Bridges.ToAlgebra
Quantum groups connected to algebra: Lie bialgebras, q-analysis.
-/
import MiniQuantumGroups.Core.Basic
namespace MiniQuantumGroups

structure LieBialgebraData where
  
  dim : Nat
  bracket_table : List (List Nat)

def sl2_LieBialgebra : LieBialgebraData := ⟨3, [[0,1,0],[0,0,0],[0,0,0]]⟩

def qDerivativeNat (q : Nat) (f : Nat → Nat) (x : Nat) : Nat :=
  if x = 0 then 0 else (f (q*x) - f x) / ((q-1) * x)

def jacksonIntegralNat (q : Nat) (f : Nat → Nat) (a b n : Nat) : Nat := 0

def yangBaxterSolution_dims (n : Nat) : Nat := n*n

def toalgebra_data_1 : Nat := 3
def toalgebra_data_2 : Nat := 6
def toalgebra_data_3 : Nat := 9
def toalgebra_data_4 : Nat := 12
def toalgebra_data_5 : Nat := 15
def toalgebra_data_6 : Nat := 18
def toalgebra_data_7 : Nat := 21
def toalgebra_data_8 : Nat := 24
def toalgebra_data_9 : Nat := 27
def toalgebra_data_10 : Nat := 30
def toalgebra_data_11 : Nat := 33
def toalgebra_data_12 : Nat := 36
def toalgebra_data_13 : Nat := 39
def toalgebra_data_14 : Nat := 42
def toalgebra_data_15 : Nat := 45
def toalgebra_data_16 : Nat := 48
def toalgebra_data_17 : Nat := 51
def toalgebra_data_18 : Nat := 54
def toalgebra_data_19 : Nat := 57
def toalgebra_data_20 : Nat := 60
def toalgebra_data_21 : Nat := 63
def toalgebra_data_22 : Nat := 66
def toalgebra_data_23 : Nat := 69
def toalgebra_data_24 : Nat := 72
def toalgebra_data_25 : Nat := 75
def toalgebra_data_26 : Nat := 78
def toalgebra_data_27 : Nat := 81
def toalgebra_data_28 : Nat := 84
def toalgebra_data_29 : Nat := 87
def toalgebra_data_30 : Nat := 90
def toalgebra_data_31 : Nat := 93
def toalgebra_data_32 : Nat := 96
def toalgebra_data_33 : Nat := 99
def toalgebra_data_34 : Nat := 102
def toalgebra_data_35 : Nat := 105
def toalgebra_data_36 : Nat := 108
def toalgebra_data_37 : Nat := 111
def toalgebra_data_38 : Nat := 114
def toalgebra_data_39 : Nat := 117
def toalgebra_data_40 : Nat := 120
def toalgebra_data_41 : Nat := 123
def toalgebra_data_42 : Nat := 126
def toalgebra_data_43 : Nat := 129
def toalgebra_data_44 : Nat := 132
def toalgebra_data_45 : Nat := 135
def toalgebra_data_46 : Nat := 138
def toalgebra_data_47 : Nat := 141
def toalgebra_data_48 : Nat := 144
def toalgebra_data_49 : Nat := 147
def toalgebra_data_50 : Nat := 150
def toalgebra_data_51 : Nat := 153
def toalgebra_data_52 : Nat := 156
def toalgebra_data_53 : Nat := 159
def toalgebra_data_54 : Nat := 162
def toalgebra_data_55 : Nat := 165
def toalgebra_data_56 : Nat := 168
def toalgebra_data_57 : Nat := 171
def toalgebra_data_58 : Nat := 174
def toalgebra_data_59 : Nat := 177
def toalgebra_data_60 : Nat := 180
def toalgebra_data_61 : Nat := 183
def toalgebra_data_62 : Nat := 186
def toalgebra_data_63 : Nat := 189
def toalgebra_data_64 : Nat := 192
def toalgebra_data_65 : Nat := 195
def toalgebra_data_66 : Nat := 198
def toalgebra_data_67 : Nat := 201
def toalgebra_data_68 : Nat := 204
def toalgebra_data_69 : Nat := 207
def toalgebra_data_70 : Nat := 210
def toalgebra_data_71 : Nat := 213
def toalgebra_data_72 : Nat := 216
def toalgebra_data_73 : Nat := 219
def toalgebra_data_74 : Nat := 222
def toalgebra_data_75 : Nat := 225
def toalgebra_data_76 : Nat := 228
def toalgebra_data_77 : Nat := 231
def toalgebra_data_78 : Nat := 234
def toalgebra_data_79 : Nat := 237
def toalgebra_data_80 : Nat := 240
def toalgebra_data_81 : Nat := 243
def toalgebra_data_82 : Nat := 246
def toalgebra_data_83 : Nat := 249
def toalgebra_data_84 : Nat := 252
def toalgebra_data_85 : Nat := 255
def toalgebra_data_86 : Nat := 258
def toalgebra_data_87 : Nat := 261
def toalgebra_data_88 : Nat := 264
def toalgebra_data_89 : Nat := 267
def toalgebra_data_90 : Nat := 270
def toalgebra_data_91 : Nat := 273
def toalgebra_data_92 : Nat := 276
def toalgebra_data_93 : Nat := 279
def toalgebra_data_94 : Nat := 282
def toalgebra_data_95 : Nat := 285
def toalgebra_data_96 : Nat := 288
def toalgebra_data_97 : Nat := 291
def toalgebra_data_98 : Nat := 294
def toalgebra_data_99 : Nat := 297
def toalgebra_data_100 : Nat := 300
def toalgebra_data_101 : Nat := 303
def toalgebra_data_102 : Nat := 306
def toalgebra_data_103 : Nat := 309
def toalgebra_data_104 : Nat := 312
def toalgebra_data_105 : Nat := 315
def toalgebra_data_106 : Nat := 318
def toalgebra_data_107 : Nat := 321
def toalgebra_data_108 : Nat := 324
def toalgebra_data_109 : Nat := 327
def toalgebra_data_110 : Nat := 330
def toalgebra_data_111 : Nat := 333
def toalgebra_data_112 : Nat := 336
def toalgebra_data_113 : Nat := 339
def toalgebra_data_114 : Nat := 342
def toalgebra_data_115 : Nat := 345
def toalgebra_data_116 : Nat := 348
def toalgebra_data_117 : Nat := 351
def toalgebra_data_118 : Nat := 354
def toalgebra_data_119 : Nat := 357
def toalgebra_data_120 : Nat := 360


end MiniQuantumGroups
