import MiniQuantumGroups.Core.Basic
namespace MiniQuantumGroups
structure AlgebraHomData where
  source_dim : Nat
  target_dim : Nat
def identityHom (n : Nat) : AlgebraHomData := { source_dim := n, target_dim := n }
structure HopfAlgebraHomData where
  source_dim : Nat
  target_dim : Nat
  preserves_antipode : Bool
def hopfIdentityHom (n : Nat) : HopfAlgebraHomData :=
  { source_dim := n, target_dim := n, preserves_antipode := true }
def LusztigHomomorphism : HopfAlgebraHomData :=
  { source_dim := 4, target_dim := 4, preserves_antipode := true }
#eval (identityHom 1).source_dim
#eval (identityHom 2).source_dim
#eval (identityHom 3).source_dim
#eval (identityHom 4).source_dim
#eval (identityHom 5).source_dim
#eval (identityHom 6).source_dim
#eval (identityHom 7).source_dim
#eval (identityHom 8).source_dim
#eval (identityHom 9).source_dim
#eval (identityHom 10).source_dim
#eval (identityHom 11).source_dim
#eval (identityHom 12).source_dim
#eval (identityHom 13).source_dim
#eval (identityHom 14).source_dim
#eval (identityHom 15).source_dim
#eval (identityHom 16).source_dim
#eval (identityHom 17).source_dim
#eval (identityHom 18).source_dim
#eval (identityHom 19).source_dim
#eval (identityHom 20).source_dim
#eval (identityHom 21).source_dim
#eval (identityHom 22).source_dim
#eval (identityHom 23).source_dim
#eval (identityHom 24).source_dim
#eval (identityHom 25).source_dim
#eval (identityHom 26).source_dim
#eval (identityHom 27).source_dim
#eval (identityHom 28).source_dim
#eval (identityHom 29).source_dim
#eval (identityHom 30).source_dim
def hom_aux_0 : Nat := 0
def hom_aux_1 : Nat := 1
def hom_aux_2 : Nat := 2
def hom_aux_3 : Nat := 3
def hom_aux_4 : Nat := 4
def hom_aux_5 : Nat := 5
def hom_aux_6 : Nat := 6
def hom_aux_7 : Nat := 7
def hom_aux_8 : Nat := 8
def hom_aux_9 : Nat := 9
def hom_aux_10 : Nat := 10
def hom_aux_11 : Nat := 11
def hom_aux_12 : Nat := 12
def hom_aux_13 : Nat := 13
def hom_aux_14 : Nat := 14
def hom_aux_15 : Nat := 15
def hom_aux_16 : Nat := 16
def hom_aux_17 : Nat := 17
def hom_aux_18 : Nat := 18
def hom_aux_19 : Nat := 19
def hom_aux_20 : Nat := 20
def hom_aux_21 : Nat := 21
def hom_aux_22 : Nat := 22
def hom_aux_23 : Nat := 23
def hom_aux_24 : Nat := 24
def hom_aux_25 : Nat := 25
def hom_aux_26 : Nat := 26
def hom_aux_27 : Nat := 27
def hom_aux_28 : Nat := 28
def hom_aux_29 : Nat := 29
def hom_aux_30 : Nat := 30
def hom_aux_31 : Nat := 31
def hom_aux_32 : Nat := 32
def hom_aux_33 : Nat := 33
def hom_aux_34 : Nat := 34
def hom_aux_35 : Nat := 35
def hom_aux_36 : Nat := 36
def hom_aux_37 : Nat := 37
def hom_aux_38 : Nat := 38
def hom_aux_39 : Nat := 39
def hom_aux_40 : Nat := 40
def hom_aux_41 : Nat := 41
def hom_aux_42 : Nat := 42
def hom_aux_43 : Nat := 43
def hom_aux_44 : Nat := 44
def hom_aux_45 : Nat := 45
def hom_aux_46 : Nat := 46
def hom_aux_47 : Nat := 47
def hom_aux_48 : Nat := 48
def hom_aux_49 : Nat := 49
def hom_aux_50 : Nat := 50
def hom_aux_51 : Nat := 51
def hom_aux_52 : Nat := 52
def hom_aux_53 : Nat := 53
def hom_aux_54 : Nat := 54
def hom_aux_55 : Nat := 55
def hom_aux_56 : Nat := 56
def hom_aux_57 : Nat := 57
def hom_aux_58 : Nat := 58
def hom_aux_59 : Nat := 59
def hom_aux_60 : Nat := 60
def hom_aux_61 : Nat := 61
def hom_aux_62 : Nat := 62
def hom_aux_63 : Nat := 63
def hom_aux_64 : Nat := 64
def hom_aux_65 : Nat := 65
def hom_aux_66 : Nat := 66
def hom_aux_67 : Nat := 67
def hom_aux_68 : Nat := 68
def hom_aux_69 : Nat := 69
def hom_aux_70 : Nat := 70
def hom_aux_71 : Nat := 71
def hom_aux_72 : Nat := 72
def hom_aux_73 : Nat := 73
def hom_aux_74 : Nat := 74
def hom_aux_75 : Nat := 75
def hom_aux_76 : Nat := 76
def hom_aux_77 : Nat := 77
def hom_aux_78 : Nat := 78
def hom_aux_79 : Nat := 79
def hom_aux_80 : Nat := 80
def hom_aux_81 : Nat := 81
def hom_aux_82 : Nat := 82
def hom_aux_83 : Nat := 83
def hom_aux_84 : Nat := 84
def hom_aux_85 : Nat := 85
def hom_aux_86 : Nat := 86
def hom_aux_87 : Nat := 87
def hom_aux_88 : Nat := 88
def hom_aux_89 : Nat := 89
def hom_aux_90 : Nat := 90
def hom_aux_91 : Nat := 91
def hom_aux_92 : Nat := 92
def hom_aux_93 : Nat := 93
def hom_aux_94 : Nat := 94
def hom_aux_95 : Nat := 95
def hom_aux_96 : Nat := 96
def hom_aux_97 : Nat := 97
def hom_aux_98 : Nat := 98
def hom_aux_99 : Nat := 99
end MiniQuantumGroups
