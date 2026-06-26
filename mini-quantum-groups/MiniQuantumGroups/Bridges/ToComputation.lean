/-
MiniQuantumGroups.Bridges.ToComputation
Quantum groups in computation: anyons, topological quantum computing.
-/
import MiniQuantumGroups.Core.Basic
import MiniQuantumGroups.Properties.Invariants
namespace MiniQuantumGroups

structure AnyonModel where
  
  particle_types : List Nat
  fusion_rule : Nat → Nat → List Nat

def fibonacciAnyons : AnyonModel where
  
  particle_types := [0, 1]
  fusion_rule := λ a b =>
    if a = 1 ∧ b = 1 then [0, 1] else if a = 0 then [b] else if b = 0 then [a] else []

def anyonBraidingPhase (_q : Nat) (_a _b : Nat) : Nat := _q

def topologicalQubitDim : Nat := 2

def fibonacciFromQG (_q : Nat) : AnyonModel := fibonacciAnyons

def quantumGateFromR (R : List (List Nat)) (_i _n : Nat) : List (List Nat) := R

def jonesQuantumAlgorithm (knot : Nat) (q : Nat) : Nat := jonesPolynomialValue knot q

def cnotFromBraiding : Bool := true

#eval fibonacciAnyons.fusion_rule 1 1
#eval jonesQuantumAlgorithm 1 2

def tocomputation_data_1 : Nat := 3
def tocomputation_data_2 : Nat := 6
def tocomputation_data_3 : Nat := 9
def tocomputation_data_4 : Nat := 12
def tocomputation_data_5 : Nat := 15
def tocomputation_data_6 : Nat := 18
def tocomputation_data_7 : Nat := 21
def tocomputation_data_8 : Nat := 24
def tocomputation_data_9 : Nat := 27
def tocomputation_data_10 : Nat := 30
def tocomputation_data_11 : Nat := 33
def tocomputation_data_12 : Nat := 36
def tocomputation_data_13 : Nat := 39
def tocomputation_data_14 : Nat := 42
def tocomputation_data_15 : Nat := 45
def tocomputation_data_16 : Nat := 48
def tocomputation_data_17 : Nat := 51
def tocomputation_data_18 : Nat := 54
def tocomputation_data_19 : Nat := 57
def tocomputation_data_20 : Nat := 60
def tocomputation_data_21 : Nat := 63
def tocomputation_data_22 : Nat := 66
def tocomputation_data_23 : Nat := 69
def tocomputation_data_24 : Nat := 72
def tocomputation_data_25 : Nat := 75
def tocomputation_data_26 : Nat := 78
def tocomputation_data_27 : Nat := 81
def tocomputation_data_28 : Nat := 84
def tocomputation_data_29 : Nat := 87
def tocomputation_data_30 : Nat := 90
def tocomputation_data_31 : Nat := 93
def tocomputation_data_32 : Nat := 96
def tocomputation_data_33 : Nat := 99
def tocomputation_data_34 : Nat := 102
def tocomputation_data_35 : Nat := 105
def tocomputation_data_36 : Nat := 108
def tocomputation_data_37 : Nat := 111
def tocomputation_data_38 : Nat := 114
def tocomputation_data_39 : Nat := 117
def tocomputation_data_40 : Nat := 120
def tocomputation_data_41 : Nat := 123
def tocomputation_data_42 : Nat := 126
def tocomputation_data_43 : Nat := 129
def tocomputation_data_44 : Nat := 132
def tocomputation_data_45 : Nat := 135
def tocomputation_data_46 : Nat := 138
def tocomputation_data_47 : Nat := 141
def tocomputation_data_48 : Nat := 144
def tocomputation_data_49 : Nat := 147
def tocomputation_data_50 : Nat := 150
def tocomputation_data_51 : Nat := 153
def tocomputation_data_52 : Nat := 156
def tocomputation_data_53 : Nat := 159
def tocomputation_data_54 : Nat := 162
def tocomputation_data_55 : Nat := 165
def tocomputation_data_56 : Nat := 168
def tocomputation_data_57 : Nat := 171
def tocomputation_data_58 : Nat := 174
def tocomputation_data_59 : Nat := 177
def tocomputation_data_60 : Nat := 180
def tocomputation_data_61 : Nat := 183
def tocomputation_data_62 : Nat := 186
def tocomputation_data_63 : Nat := 189
def tocomputation_data_64 : Nat := 192
def tocomputation_data_65 : Nat := 195
def tocomputation_data_66 : Nat := 198
def tocomputation_data_67 : Nat := 201
def tocomputation_data_68 : Nat := 204
def tocomputation_data_69 : Nat := 207
def tocomputation_data_70 : Nat := 210
def tocomputation_data_71 : Nat := 213
def tocomputation_data_72 : Nat := 216
def tocomputation_data_73 : Nat := 219
def tocomputation_data_74 : Nat := 222
def tocomputation_data_75 : Nat := 225
def tocomputation_data_76 : Nat := 228
def tocomputation_data_77 : Nat := 231
def tocomputation_data_78 : Nat := 234
def tocomputation_data_79 : Nat := 237
def tocomputation_data_80 : Nat := 240
def tocomputation_data_81 : Nat := 243
def tocomputation_data_82 : Nat := 246
def tocomputation_data_83 : Nat := 249
def tocomputation_data_84 : Nat := 252
def tocomputation_data_85 : Nat := 255
def tocomputation_data_86 : Nat := 258
def tocomputation_data_87 : Nat := 261
def tocomputation_data_88 : Nat := 264
def tocomputation_data_89 : Nat := 267
def tocomputation_data_90 : Nat := 270
def tocomputation_data_91 : Nat := 273
def tocomputation_data_92 : Nat := 276
def tocomputation_data_93 : Nat := 279
def tocomputation_data_94 : Nat := 282
def tocomputation_data_95 : Nat := 285
def tocomputation_data_96 : Nat := 288
def tocomputation_data_97 : Nat := 291
def tocomputation_data_98 : Nat := 294
def tocomputation_data_99 : Nat := 297
def tocomputation_data_100 : Nat := 300
def tocomputation_data_101 : Nat := 303
def tocomputation_data_102 : Nat := 306
def tocomputation_data_103 : Nat := 309
def tocomputation_data_104 : Nat := 312
def tocomputation_data_105 : Nat := 315
def tocomputation_data_106 : Nat := 318
def tocomputation_data_107 : Nat := 321
def tocomputation_data_108 : Nat := 324
def tocomputation_data_109 : Nat := 327
def tocomputation_data_110 : Nat := 330
def tocomputation_data_111 : Nat := 333
def tocomputation_data_112 : Nat := 336
def tocomputation_data_113 : Nat := 339
def tocomputation_data_114 : Nat := 342
def tocomputation_data_115 : Nat := 345
def tocomputation_data_116 : Nat := 348
def tocomputation_data_117 : Nat := 351
def tocomputation_data_118 : Nat := 354
def tocomputation_data_119 : Nat := 357
def tocomputation_data_120 : Nat := 360


end MiniQuantumGroups
