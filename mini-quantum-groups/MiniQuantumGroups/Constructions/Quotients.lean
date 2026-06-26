import MiniQuantumGroups.Core.Basic
namespace MiniQuantumGroups
structure QuotientQGData where
  G_dim : Nat
  K_dim : Nat
  quotient_dim : Nat
def quotient_example : QuotientQGData :=
  { G_dim := 4, K_dim := 1, quotient_dim := 3 }
structure QuantumHomogeneousSpace where
  total_dim : Nat
  fiber_dim : Nat
  base_dim : Nat
def quantumSphereExample : QuantumHomogeneousSpace :=
  { total_dim := 4, fiber_dim := 1, base_dim := 3 }
def quantumProjSpaceExample (n : Nat) : QuantumHomogeneousSpace :=
  { total_dim := (n+1)*(n+1), fiber_dim := 1, base_dim := n*(n+2) }
#eval (quantumProjSpaceExample 2).base_dim
def quotients_val_0 : Nat := 0
def quotients_val_1 : Nat := 1
def quotients_val_2 : Nat := 2
def quotients_val_3 : Nat := 3
def quotients_val_4 : Nat := 4
def quotients_val_5 : Nat := 5
def quotients_val_6 : Nat := 6
def quotients_val_7 : Nat := 7
def quotients_val_8 : Nat := 8
def quotients_val_9 : Nat := 9
def quotients_val_10 : Nat := 10
def quotients_val_11 : Nat := 11
def quotients_val_12 : Nat := 12
def quotients_val_13 : Nat := 13
def quotients_val_14 : Nat := 14
def quotients_val_15 : Nat := 15
def quotients_val_16 : Nat := 16
def quotients_val_17 : Nat := 17
def quotients_val_18 : Nat := 18
def quotients_val_19 : Nat := 19
def quotients_val_20 : Nat := 20
def quotients_val_21 : Nat := 21
def quotients_val_22 : Nat := 22
def quotients_val_23 : Nat := 23
def quotients_val_24 : Nat := 24
def quotients_val_25 : Nat := 25
def quotients_val_26 : Nat := 26
def quotients_val_27 : Nat := 27
def quotients_val_28 : Nat := 28
def quotients_val_29 : Nat := 29
def quotients_val_30 : Nat := 30
def quotients_val_31 : Nat := 31
def quotients_val_32 : Nat := 32
def quotients_val_33 : Nat := 33
def quotients_val_34 : Nat := 34
def quotients_val_35 : Nat := 35
def quotients_val_36 : Nat := 36
def quotients_val_37 : Nat := 37
def quotients_val_38 : Nat := 38
def quotients_val_39 : Nat := 39
def quotients_val_40 : Nat := 40
def quotients_val_41 : Nat := 41
def quotients_val_42 : Nat := 42
def quotients_val_43 : Nat := 43
def quotients_val_44 : Nat := 44
def quotients_val_45 : Nat := 45
def quotients_val_46 : Nat := 46
def quotients_val_47 : Nat := 47
def quotients_val_48 : Nat := 48
def quotients_val_49 : Nat := 49
def quotients_val_50 : Nat := 50
def quotients_val_51 : Nat := 51
def quotients_val_52 : Nat := 52
def quotients_val_53 : Nat := 53
def quotients_val_54 : Nat := 54
def quotients_val_55 : Nat := 55
def quotients_val_56 : Nat := 56
def quotients_val_57 : Nat := 57
def quotients_val_58 : Nat := 58
def quotients_val_59 : Nat := 59
def quotients_val_60 : Nat := 60
def quotients_val_61 : Nat := 61
def quotients_val_62 : Nat := 62
def quotients_val_63 : Nat := 63
def quotients_val_64 : Nat := 64
def quotients_val_65 : Nat := 65
def quotients_val_66 : Nat := 66
def quotients_val_67 : Nat := 67
def quotients_val_68 : Nat := 68
def quotients_val_69 : Nat := 69
def quotients_val_70 : Nat := 70
def quotients_val_71 : Nat := 71
def quotients_val_72 : Nat := 72
def quotients_val_73 : Nat := 73
def quotients_val_74 : Nat := 74
def quotients_val_75 : Nat := 75
def quotients_val_76 : Nat := 76
def quotients_val_77 : Nat := 77
def quotients_val_78 : Nat := 78
def quotients_val_79 : Nat := 79
def quotients_val_80 : Nat := 80
def quotients_val_81 : Nat := 81
def quotients_val_82 : Nat := 82
def quotients_val_83 : Nat := 83
def quotients_val_84 : Nat := 84
def quotients_val_85 : Nat := 85
def quotients_val_86 : Nat := 86
def quotients_val_87 : Nat := 87
def quotients_val_88 : Nat := 88
def quotients_val_89 : Nat := 89
def quotients_val_90 : Nat := 90
def quotients_val_91 : Nat := 91
def quotients_val_92 : Nat := 92
def quotients_val_93 : Nat := 93
def quotients_val_94 : Nat := 94
def quotients_val_95 : Nat := 95
def quotients_val_96 : Nat := 96
def quotients_val_97 : Nat := 97
def quotients_val_98 : Nat := 98
def quotients_val_99 : Nat := 99
end MiniQuantumGroups
