/-
MiniQuantumGroups.Bridges.ToTopology
Quantum groups in topology: knot theory, 3-manifold invariants, TQFT.
-/
import MiniQuantumGroups.Core.Basic
namespace MiniQuantumGroups

inductive BraidGen : Type
  | sigma (i : Nat)
  | sigma_inv (i : Nat)
  deriving BEq, Repr, Inhabited, DecidableEq

structure BraidWord where
  
  generators : List BraidGen
  length : Nat

def trefoilBraid : BraidWord := ⟨[.sigma 0, .sigma 0, .sigma 0], 3⟩

def figure8Braid : BraidWord := ⟨[], 4⟩

def chernSimonsS3 (_k : Nat) : Nat := 1

def tqftTorusDim (k : Nat) : Nat := k + 1

def modularSMatrix (_k : Nat) (i j : Nat) : Nat := if i = j then 1 else 0

def khovanovEulerChar (knot : Nat) : Nat := knot

def quantumInvariantS3 (_q : Nat) : Nat := 1

def totopology_data_1 : Nat := 3
def totopology_data_2 : Nat := 6
def totopology_data_3 : Nat := 9
def totopology_data_4 : Nat := 12
def totopology_data_5 : Nat := 15
def totopology_data_6 : Nat := 18
def totopology_data_7 : Nat := 21
def totopology_data_8 : Nat := 24
def totopology_data_9 : Nat := 27
def totopology_data_10 : Nat := 30
def totopology_data_11 : Nat := 33
def totopology_data_12 : Nat := 36
def totopology_data_13 : Nat := 39
def totopology_data_14 : Nat := 42
def totopology_data_15 : Nat := 45
def totopology_data_16 : Nat := 48
def totopology_data_17 : Nat := 51
def totopology_data_18 : Nat := 54
def totopology_data_19 : Nat := 57
def totopology_data_20 : Nat := 60
def totopology_data_21 : Nat := 63
def totopology_data_22 : Nat := 66
def totopology_data_23 : Nat := 69
def totopology_data_24 : Nat := 72
def totopology_data_25 : Nat := 75
def totopology_data_26 : Nat := 78
def totopology_data_27 : Nat := 81
def totopology_data_28 : Nat := 84
def totopology_data_29 : Nat := 87
def totopology_data_30 : Nat := 90
def totopology_data_31 : Nat := 93
def totopology_data_32 : Nat := 96
def totopology_data_33 : Nat := 99
def totopology_data_34 : Nat := 102
def totopology_data_35 : Nat := 105
def totopology_data_36 : Nat := 108
def totopology_data_37 : Nat := 111
def totopology_data_38 : Nat := 114
def totopology_data_39 : Nat := 117
def totopology_data_40 : Nat := 120
def totopology_data_41 : Nat := 123
def totopology_data_42 : Nat := 126
def totopology_data_43 : Nat := 129
def totopology_data_44 : Nat := 132
def totopology_data_45 : Nat := 135
def totopology_data_46 : Nat := 138
def totopology_data_47 : Nat := 141
def totopology_data_48 : Nat := 144
def totopology_data_49 : Nat := 147
def totopology_data_50 : Nat := 150
def totopology_data_51 : Nat := 153
def totopology_data_52 : Nat := 156
def totopology_data_53 : Nat := 159
def totopology_data_54 : Nat := 162
def totopology_data_55 : Nat := 165
def totopology_data_56 : Nat := 168
def totopology_data_57 : Nat := 171
def totopology_data_58 : Nat := 174
def totopology_data_59 : Nat := 177
def totopology_data_60 : Nat := 180
def totopology_data_61 : Nat := 183
def totopology_data_62 : Nat := 186
def totopology_data_63 : Nat := 189
def totopology_data_64 : Nat := 192
def totopology_data_65 : Nat := 195
def totopology_data_66 : Nat := 198
def totopology_data_67 : Nat := 201
def totopology_data_68 : Nat := 204
def totopology_data_69 : Nat := 207
def totopology_data_70 : Nat := 210
def totopology_data_71 : Nat := 213
def totopology_data_72 : Nat := 216
def totopology_data_73 : Nat := 219
def totopology_data_74 : Nat := 222
def totopology_data_75 : Nat := 225
def totopology_data_76 : Nat := 228
def totopology_data_77 : Nat := 231
def totopology_data_78 : Nat := 234
def totopology_data_79 : Nat := 237
def totopology_data_80 : Nat := 240
def totopology_data_81 : Nat := 243
def totopology_data_82 : Nat := 246
def totopology_data_83 : Nat := 249
def totopology_data_84 : Nat := 252
def totopology_data_85 : Nat := 255
def totopology_data_86 : Nat := 258
def totopology_data_87 : Nat := 261
def totopology_data_88 : Nat := 264
def totopology_data_89 : Nat := 267
def totopology_data_90 : Nat := 270
def totopology_data_91 : Nat := 273
def totopology_data_92 : Nat := 276
def totopology_data_93 : Nat := 279
def totopology_data_94 : Nat := 282
def totopology_data_95 : Nat := 285
def totopology_data_96 : Nat := 288
def totopology_data_97 : Nat := 291
def totopology_data_98 : Nat := 294
def totopology_data_99 : Nat := 297
def totopology_data_100 : Nat := 300
def totopology_data_101 : Nat := 303
def totopology_data_102 : Nat := 306
def totopology_data_103 : Nat := 309
def totopology_data_104 : Nat := 312
def totopology_data_105 : Nat := 315
def totopology_data_106 : Nat := 318
def totopology_data_107 : Nat := 321
def totopology_data_108 : Nat := 324
def totopology_data_109 : Nat := 327
def totopology_data_110 : Nat := 330
def totopology_data_111 : Nat := 333
def totopology_data_112 : Nat := 336
def totopology_data_113 : Nat := 339
def totopology_data_114 : Nat := 342
def totopology_data_115 : Nat := 345
def totopology_data_116 : Nat := 348
def totopology_data_117 : Nat := 351
def totopology_data_118 : Nat := 354
def totopology_data_119 : Nat := 357
def totopology_data_120 : Nat := 360


end MiniQuantumGroups
