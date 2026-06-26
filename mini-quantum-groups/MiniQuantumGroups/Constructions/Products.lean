import MiniQuantumGroups.Core.Basic
namespace MiniQuantumGroups
structure TensorProductData where
  dim1 : Nat
  dim2 : Nat
  prod_dim : Nat
def tensorProdReps (r1 r2 : Nat) : TensorProductData :=
  { dim1 := r1, dim2 := r2, prod_dim := r1 * r2 }
structure SmashProductData where
  A_dim : Nat
  H_dim : Nat
  prod_dim : Nat
def smashProductExample : SmashProductData :=
  { A_dim := 2, H_dim := 3, prod_dim := 6 }
#eval (tensorProdReps 2 3).prod_dim
#eval smashProductExample.prod_dim
def products_val_0 : Nat := 0
def products_val_1 : Nat := 1
def products_val_2 : Nat := 2
def products_val_3 : Nat := 3
def products_val_4 : Nat := 4
def products_val_5 : Nat := 5
def products_val_6 : Nat := 6
def products_val_7 : Nat := 7
def products_val_8 : Nat := 8
def products_val_9 : Nat := 9
def products_val_10 : Nat := 10
def products_val_11 : Nat := 11
def products_val_12 : Nat := 12
def products_val_13 : Nat := 13
def products_val_14 : Nat := 14
def products_val_15 : Nat := 15
def products_val_16 : Nat := 16
def products_val_17 : Nat := 17
def products_val_18 : Nat := 18
def products_val_19 : Nat := 19
def products_val_20 : Nat := 20
def products_val_21 : Nat := 21
def products_val_22 : Nat := 22
def products_val_23 : Nat := 23
def products_val_24 : Nat := 24
def products_val_25 : Nat := 25
def products_val_26 : Nat := 26
def products_val_27 : Nat := 27
def products_val_28 : Nat := 28
def products_val_29 : Nat := 29
def products_val_30 : Nat := 30
def products_val_31 : Nat := 31
def products_val_32 : Nat := 32
def products_val_33 : Nat := 33
def products_val_34 : Nat := 34
def products_val_35 : Nat := 35
def products_val_36 : Nat := 36
def products_val_37 : Nat := 37
def products_val_38 : Nat := 38
def products_val_39 : Nat := 39
def products_val_40 : Nat := 40
def products_val_41 : Nat := 41
def products_val_42 : Nat := 42
def products_val_43 : Nat := 43
def products_val_44 : Nat := 44
def products_val_45 : Nat := 45
def products_val_46 : Nat := 46
def products_val_47 : Nat := 47
def products_val_48 : Nat := 48
def products_val_49 : Nat := 49
def products_val_50 : Nat := 50
def products_val_51 : Nat := 51
def products_val_52 : Nat := 52
def products_val_53 : Nat := 53
def products_val_54 : Nat := 54
def products_val_55 : Nat := 55
def products_val_56 : Nat := 56
def products_val_57 : Nat := 57
def products_val_58 : Nat := 58
def products_val_59 : Nat := 59
def products_val_60 : Nat := 60
def products_val_61 : Nat := 61
def products_val_62 : Nat := 62
def products_val_63 : Nat := 63
def products_val_64 : Nat := 64
def products_val_65 : Nat := 65
def products_val_66 : Nat := 66
def products_val_67 : Nat := 67
def products_val_68 : Nat := 68
def products_val_69 : Nat := 69
def products_val_70 : Nat := 70
def products_val_71 : Nat := 71
def products_val_72 : Nat := 72
def products_val_73 : Nat := 73
def products_val_74 : Nat := 74
def products_val_75 : Nat := 75
def products_val_76 : Nat := 76
def products_val_77 : Nat := 77
def products_val_78 : Nat := 78
def products_val_79 : Nat := 79
def products_val_80 : Nat := 80
def products_val_81 : Nat := 81
def products_val_82 : Nat := 82
def products_val_83 : Nat := 83
def products_val_84 : Nat := 84
def products_val_85 : Nat := 85
def products_val_86 : Nat := 86
def products_val_87 : Nat := 87
def products_val_88 : Nat := 88
def products_val_89 : Nat := 89
def products_val_90 : Nat := 90
def products_val_91 : Nat := 91
def products_val_92 : Nat := 92
def products_val_93 : Nat := 93
def products_val_94 : Nat := 94
def products_val_95 : Nat := 95
def products_val_96 : Nat := 96
def products_val_97 : Nat := 97
def products_val_98 : Nat := 98
def products_val_99 : Nat := 99
end MiniQuantumGroups
