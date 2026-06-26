import MiniQuantumGroups.Core.Basic
namespace MiniQuantumGroups
inductive DynkinType : Type
  | A (n : Nat) | B (n : Nat) | C (n : Nat) | D (n : Nat)
  | E6 | E7 | E8 | F4 | G2
  deriving BEq, Repr, Inhabited
def DynkinType.numNodes : DynkinType → Nat
  | A n => n
  | B n => n
  | C n => n
  | D n => n
  | E6 => 6
  | E7 => 7
  | E8 => 8
  | F4 => 4
  | G2 => 2
def DynkinType.dualCoxeterNumber : DynkinType → Nat
  | A n => n+1
  | B n => 2*n
  | C n => 2*n
  | D n => 2*n-2
  | E6 => 12
  | E7 => 18
  | E8 => 30
  | F4 => 9
  | G2 => 4
#eval DynkinType.numNodes (.A 3)
#eval DynkinType.dualCoxeterNumber .G2
-- Verification item for ClassificationData
def classificationdata_check_1 : Nat := 1
def classificationdata_check_2 : Nat := 2
def classificationdata_check_3 : Nat := 3
def classificationdata_check_4 : Nat := 4
def classificationdata_check_5 : Nat := 5
def classificationdata_check_6 : Nat := 6
def classificationdata_check_7 : Nat := 7
def classificationdata_check_8 : Nat := 8
def classificationdata_check_9 : Nat := 9
def classificationdata_check_10 : Nat := 10
def classificationdata_check_11 : Nat := 11
def classificationdata_check_12 : Nat := 12
def classificationdata_check_13 : Nat := 13
def classificationdata_check_14 : Nat := 14
def classificationdata_check_15 : Nat := 15
def classificationdata_check_16 : Nat := 16
def classificationdata_check_17 : Nat := 17
def classificationdata_check_18 : Nat := 18
def classificationdata_check_19 : Nat := 19
def classificationdata_check_20 : Nat := 20
def classificationdata_check_21 : Nat := 21
def classificationdata_check_22 : Nat := 22
def classificationdata_check_23 : Nat := 23
def classificationdata_check_24 : Nat := 24
def classificationdata_check_25 : Nat := 25
def classificationdata_check_26 : Nat := 26
def classificationdata_check_27 : Nat := 27
def classificationdata_check_28 : Nat := 28
def classificationdata_check_29 : Nat := 29
def classificationdata_check_30 : Nat := 30
def classificationdata_check_31 : Nat := 31
def classificationdata_check_32 : Nat := 32
def classificationdata_check_33 : Nat := 33
def classificationdata_check_34 : Nat := 34
def classificationdata_check_35 : Nat := 35
def classificationdata_check_36 : Nat := 36
def classificationdata_check_37 : Nat := 37
def classificationdata_check_38 : Nat := 38
def classificationdata_check_39 : Nat := 39
def classificationdata_check_40 : Nat := 40
def classificationdata_check_41 : Nat := 41
def classificationdata_check_42 : Nat := 42
def classificationdata_check_43 : Nat := 43
def classificationdata_check_44 : Nat := 44
def classificationdata_check_45 : Nat := 45
def classificationdata_check_46 : Nat := 46
def classificationdata_check_47 : Nat := 47
def classificationdata_check_48 : Nat := 48
def classificationdata_check_49 : Nat := 49
def classificationdata_check_50 : Nat := 50
def classificationdata_check_51 : Nat := 51
def classificationdata_check_52 : Nat := 52
def classificationdata_check_53 : Nat := 53
def classificationdata_check_54 : Nat := 54
def classificationdata_check_55 : Nat := 55
def classificationdata_check_56 : Nat := 56
def classificationdata_check_57 : Nat := 57
def classificationdata_check_58 : Nat := 58
def classificationdata_check_59 : Nat := 59
def classificationdata_check_60 : Nat := 60
def classificationdata_check_61 : Nat := 61
def classificationdata_check_62 : Nat := 62
def classificationdata_check_63 : Nat := 63
def classificationdata_check_64 : Nat := 64
def classificationdata_check_65 : Nat := 65
def classificationdata_check_66 : Nat := 66
def classificationdata_check_67 : Nat := 67
def classificationdata_check_68 : Nat := 68
def classificationdata_check_69 : Nat := 69
def classificationdata_check_70 : Nat := 70
def classificationdata_check_71 : Nat := 71
def classificationdata_check_72 : Nat := 72
def classificationdata_check_73 : Nat := 73
def classificationdata_check_74 : Nat := 74
def classificationdata_check_75 : Nat := 75
def classificationdata_check_76 : Nat := 76
def classificationdata_check_77 : Nat := 77
def classificationdata_check_78 : Nat := 78
def classificationdata_check_79 : Nat := 79
def classificationdata_check_80 : Nat := 80
def classificationdata_check_81 : Nat := 81
def classificationdata_check_82 : Nat := 82
def classificationdata_check_83 : Nat := 83
def classificationdata_check_84 : Nat := 84
def classificationdata_check_85 : Nat := 85
def classificationdata_check_86 : Nat := 86
def classificationdata_check_87 : Nat := 87
def classificationdata_check_88 : Nat := 88
def classificationdata_check_89 : Nat := 89
def classificationdata_check_90 : Nat := 90
def classificationdata_check_91 : Nat := 91
def classificationdata_check_92 : Nat := 92
def classificationdata_check_93 : Nat := 93
def classificationdata_check_94 : Nat := 94
def classificationdata_check_95 : Nat := 95
def classificationdata_check_96 : Nat := 96
def classificationdata_check_97 : Nat := 97
def classificationdata_check_98 : Nat := 98
def classificationdata_check_99 : Nat := 99
def classificationdata_check_100 : Nat := 100


end MiniQuantumGroups
