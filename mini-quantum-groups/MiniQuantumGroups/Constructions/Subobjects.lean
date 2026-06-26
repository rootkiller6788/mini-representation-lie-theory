import MiniQuantumGroups.Core.Basic
namespace MiniQuantumGroups
inductive FiniteQGSubgroup : Type
  | cyclic (n : Nat)
  | binary_dihedral (n : Nat)
  | binary_tetrahedral
  | binary_octahedral
  | binary_icosahedral
  deriving BEq, Repr, Inhabited
def ADE_classification : List FiniteQGSubgroup := [
  .cyclic 1, .cyclic 2, .cyclic 3,
  .binary_dihedral 2, .binary_dihedral 3,
  .binary_tetrahedral, .binary_octahedral, .binary_icosahedral]
structure HopfSubalgebraData where
  parent_dim : Nat
  subalg_dim : Nat
def cartanSubalg : HopfSubalgebraData := { parent_dim := 4, subalg_dim := 2 }
#eval ADE_classification.length
def subobjects_val_0 : Nat := 0
def subobjects_val_1 : Nat := 1
def subobjects_val_2 : Nat := 2
def subobjects_val_3 : Nat := 3
def subobjects_val_4 : Nat := 4
def subobjects_val_5 : Nat := 5
def subobjects_val_6 : Nat := 6
def subobjects_val_7 : Nat := 7
def subobjects_val_8 : Nat := 8
def subobjects_val_9 : Nat := 9
def subobjects_val_10 : Nat := 10
def subobjects_val_11 : Nat := 11
def subobjects_val_12 : Nat := 12
def subobjects_val_13 : Nat := 13
def subobjects_val_14 : Nat := 14
def subobjects_val_15 : Nat := 15
def subobjects_val_16 : Nat := 16
def subobjects_val_17 : Nat := 17
def subobjects_val_18 : Nat := 18
def subobjects_val_19 : Nat := 19
def subobjects_val_20 : Nat := 20
def subobjects_val_21 : Nat := 21
def subobjects_val_22 : Nat := 22
def subobjects_val_23 : Nat := 23
def subobjects_val_24 : Nat := 24
def subobjects_val_25 : Nat := 25
def subobjects_val_26 : Nat := 26
def subobjects_val_27 : Nat := 27
def subobjects_val_28 : Nat := 28
def subobjects_val_29 : Nat := 29
def subobjects_val_30 : Nat := 30
def subobjects_val_31 : Nat := 31
def subobjects_val_32 : Nat := 32
def subobjects_val_33 : Nat := 33
def subobjects_val_34 : Nat := 34
def subobjects_val_35 : Nat := 35
def subobjects_val_36 : Nat := 36
def subobjects_val_37 : Nat := 37
def subobjects_val_38 : Nat := 38
def subobjects_val_39 : Nat := 39
def subobjects_val_40 : Nat := 40
def subobjects_val_41 : Nat := 41
def subobjects_val_42 : Nat := 42
def subobjects_val_43 : Nat := 43
def subobjects_val_44 : Nat := 44
def subobjects_val_45 : Nat := 45
def subobjects_val_46 : Nat := 46
def subobjects_val_47 : Nat := 47
def subobjects_val_48 : Nat := 48
def subobjects_val_49 : Nat := 49
def subobjects_val_50 : Nat := 50
def subobjects_val_51 : Nat := 51
def subobjects_val_52 : Nat := 52
def subobjects_val_53 : Nat := 53
def subobjects_val_54 : Nat := 54
def subobjects_val_55 : Nat := 55
def subobjects_val_56 : Nat := 56
def subobjects_val_57 : Nat := 57
def subobjects_val_58 : Nat := 58
def subobjects_val_59 : Nat := 59
def subobjects_val_60 : Nat := 60
def subobjects_val_61 : Nat := 61
def subobjects_val_62 : Nat := 62
def subobjects_val_63 : Nat := 63
def subobjects_val_64 : Nat := 64
def subobjects_val_65 : Nat := 65
def subobjects_val_66 : Nat := 66
def subobjects_val_67 : Nat := 67
def subobjects_val_68 : Nat := 68
def subobjects_val_69 : Nat := 69
def subobjects_val_70 : Nat := 70
def subobjects_val_71 : Nat := 71
def subobjects_val_72 : Nat := 72
def subobjects_val_73 : Nat := 73
def subobjects_val_74 : Nat := 74
def subobjects_val_75 : Nat := 75
def subobjects_val_76 : Nat := 76
def subobjects_val_77 : Nat := 77
def subobjects_val_78 : Nat := 78
def subobjects_val_79 : Nat := 79
def subobjects_val_80 : Nat := 80
def subobjects_val_81 : Nat := 81
def subobjects_val_82 : Nat := 82
def subobjects_val_83 : Nat := 83
def subobjects_val_84 : Nat := 84
def subobjects_val_85 : Nat := 85
def subobjects_val_86 : Nat := 86
def subobjects_val_87 : Nat := 87
def subobjects_val_88 : Nat := 88
def subobjects_val_89 : Nat := 89
def subobjects_val_90 : Nat := 90
def subobjects_val_91 : Nat := 91
def subobjects_val_92 : Nat := 92
def subobjects_val_93 : Nat := 93
def subobjects_val_94 : Nat := 94
def subobjects_val_95 : Nat := 95
def subobjects_val_96 : Nat := 96
def subobjects_val_97 : Nat := 97
def subobjects_val_98 : Nat := 98
def subobjects_val_99 : Nat := 99
end MiniQuantumGroups
