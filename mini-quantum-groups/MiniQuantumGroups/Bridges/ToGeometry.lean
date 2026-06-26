import MiniQuantumGroups.Core.Basic
namespace MiniQuantumGroups
structure NCAlgebraData where
  
  dim : Nat
  commutation_table : List (List Nat)
def podlesSphereData (q : Nat) : NCAlgebraData where
  
  dim := 3; commutation_table := [[0,q,0],[q,0,0],[0,0,0]]
structure QuantumPrincipalBundle where
  
  total_dim : Nat
  base_dim : Nat
  fiber_dim : Nat
def hopfFibration_q (_q : Nat) : QuantumPrincipalBundle where
  
  total_dim := 4; base_dim := 3; fiber_dim := 1
structure QuantumFlagVariety where
  
  group_dim : Nat
  parabolic_dim : Nat
  quotient_dim : Nat
def quantumGrassmannian (k n _q : Nat) : QuantumFlagVariety where
  
  group_dim := n*n; parabolic_dim := k*k; quotient_dim := n*n - k*k
structure BicovariantCalc where
  
  dim : Nat
  first_order_dim : Nat
def woronowiczCalc_sl2 (_q : Nat) : BicovariantCalc where
  
  dim := 3; first_order_dim := 4
def quantumProjSpace (n _q : Nat) : QuantumFlagVariety where
  
  group_dim := (n+1)*(n+1); parabolic_dim := 1; quotient_dim := n*(n+2)
def togeometry_data_1 : Nat := 3
def togeometry_data_2 : Nat := 6
def togeometry_data_3 : Nat := 9
def togeometry_data_4 : Nat := 12
def togeometry_data_5 : Nat := 15
def togeometry_data_6 : Nat := 18
def togeometry_data_7 : Nat := 21
def togeometry_data_8 : Nat := 24
def togeometry_data_9 : Nat := 27
def togeometry_data_10 : Nat := 30
def togeometry_data_11 : Nat := 33
def togeometry_data_12 : Nat := 36
def togeometry_data_13 : Nat := 39
def togeometry_data_14 : Nat := 42
def togeometry_data_15 : Nat := 45
def togeometry_data_16 : Nat := 48
def togeometry_data_17 : Nat := 51
def togeometry_data_18 : Nat := 54
def togeometry_data_19 : Nat := 57
def togeometry_data_20 : Nat := 60
def togeometry_data_21 : Nat := 63
def togeometry_data_22 : Nat := 66
def togeometry_data_23 : Nat := 69
def togeometry_data_24 : Nat := 72
def togeometry_data_25 : Nat := 75
def togeometry_data_26 : Nat := 78
def togeometry_data_27 : Nat := 81
def togeometry_data_28 : Nat := 84
def togeometry_data_29 : Nat := 87
def togeometry_data_30 : Nat := 90
def togeometry_data_31 : Nat := 93
def togeometry_data_32 : Nat := 96
def togeometry_data_33 : Nat := 99
def togeometry_data_34 : Nat := 102
def togeometry_data_35 : Nat := 105
def togeometry_data_36 : Nat := 108
def togeometry_data_37 : Nat := 111
def togeometry_data_38 : Nat := 114
def togeometry_data_39 : Nat := 117
def togeometry_data_40 : Nat := 120
def togeometry_data_41 : Nat := 123
def togeometry_data_42 : Nat := 126
def togeometry_data_43 : Nat := 129
def togeometry_data_44 : Nat := 132
def togeometry_data_45 : Nat := 135
def togeometry_data_46 : Nat := 138
def togeometry_data_47 : Nat := 141
def togeometry_data_48 : Nat := 144
def togeometry_data_49 : Nat := 147
def togeometry_data_50 : Nat := 150
def togeometry_data_51 : Nat := 153
def togeometry_data_52 : Nat := 156
def togeometry_data_53 : Nat := 159
def togeometry_data_54 : Nat := 162
def togeometry_data_55 : Nat := 165
def togeometry_data_56 : Nat := 168
def togeometry_data_57 : Nat := 171
def togeometry_data_58 : Nat := 174
def togeometry_data_59 : Nat := 177
def togeometry_data_60 : Nat := 180
def togeometry_data_61 : Nat := 183
def togeometry_data_62 : Nat := 186
def togeometry_data_63 : Nat := 189
def togeometry_data_64 : Nat := 192
def togeometry_data_65 : Nat := 195
def togeometry_data_66 : Nat := 198
def togeometry_data_67 : Nat := 201
def togeometry_data_68 : Nat := 204
def togeometry_data_69 : Nat := 207
def togeometry_data_70 : Nat := 210
def togeometry_data_71 : Nat := 213
def togeometry_data_72 : Nat := 216
def togeometry_data_73 : Nat := 219
def togeometry_data_74 : Nat := 222
def togeometry_data_75 : Nat := 225
def togeometry_data_76 : Nat := 228
def togeometry_data_77 : Nat := 231
def togeometry_data_78 : Nat := 234
def togeometry_data_79 : Nat := 237
def togeometry_data_80 : Nat := 240
def togeometry_data_81 : Nat := 243
def togeometry_data_82 : Nat := 246
def togeometry_data_83 : Nat := 249
def togeometry_data_84 : Nat := 252
def togeometry_data_85 : Nat := 255
def togeometry_data_86 : Nat := 258
def togeometry_data_87 : Nat := 261
def togeometry_data_88 : Nat := 264
def togeometry_data_89 : Nat := 267
def togeometry_data_90 : Nat := 270
def togeometry_data_91 : Nat := 273
def togeometry_data_92 : Nat := 276
def togeometry_data_93 : Nat := 279
def togeometry_data_94 : Nat := 282
def togeometry_data_95 : Nat := 285
def togeometry_data_96 : Nat := 288
def togeometry_data_97 : Nat := 291
def togeometry_data_98 : Nat := 294
def togeometry_data_99 : Nat := 297
def togeometry_data_100 : Nat := 300
def togeometry_data_101 : Nat := 303
def togeometry_data_102 : Nat := 306
def togeometry_data_103 : Nat := 309
def togeometry_data_104 : Nat := 312
def togeometry_data_105 : Nat := 315
def togeometry_data_106 : Nat := 318
def togeometry_data_107 : Nat := 321
def togeometry_data_108 : Nat := 324
def togeometry_data_109 : Nat := 327
def togeometry_data_110 : Nat := 330
def togeometry_data_111 : Nat := 333
def togeometry_data_112 : Nat := 336
def togeometry_data_113 : Nat := 339
def togeometry_data_114 : Nat := 342
def togeometry_data_115 : Nat := 345
def togeometry_data_116 : Nat := 348
def togeometry_data_117 : Nat := 351
def togeometry_data_118 : Nat := 354
def togeometry_data_119 : Nat := 357
def togeometry_data_120 : Nat := 360


end MiniQuantumGroups
