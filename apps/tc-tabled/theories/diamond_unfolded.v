(* Direct Simple Diamond example *)
Class TD (n : nat).
Class RD (n : nat).
Class LD (n : nat).
Class BD (n : nat).

Instance BD0 : BD 0 := {}.

Instance BtL0 `{BD 0} : LD 0 := {}.
Instance BtR0 `{BD 0} : RD 0 := {}.
Instance LtR0 `{LD 0} : TD 0 := {}.
Instance RtR0 `{RD 0} : TD 0 := {}.
Instance Ttb0 `{TD 0} : BD (S 0) := {}.

Instance BtL1 `{BD 1} : LD 1 := {}.
Instance BtR1 `{BD 1} : RD 1 := {}.
Instance LtR1 `{LD 1} : TD 1 := {}.
Instance RtR1 `{RD 1} : TD 1 := {}.
Instance Ttb1 `{TD 1} : BD (S 1) := {}.

Instance BtL2 `{BD 2} : LD 2 := {}.
Instance BtR2 `{BD 2} : RD 2 := {}.
Instance LtR2 `{LD 2} : TD 2 := {}.
Instance RtR2 `{RD 2} : TD 2 := {}.
Instance Ttb2 `{TD 2} : BD (S 2) := {}.

Instance BtL3 `{BD 3} : LD 3 := {}.
Instance BtR3 `{BD 3} : RD 3 := {}.
Instance LtR3 `{LD 3} : TD 3 := {}.
Instance RtR3 `{RD 3} : TD 3 := {}.
Instance Ttb3 `{TD 3} : BD (S 3) := {}.

Instance BtL4 `{BD 4} : LD 4 := {}.
Instance BtR4 `{BD 4} : RD 4 := {}.
Instance LtR4 `{LD 4} : TD 4 := {}.
Instance RtR4 `{RD 4} : TD 4 := {}.
Instance Ttb4 `{TD 4} : BD (S 4) := {}.

Instance BtL5 `{BD 5} : LD 5 := {}.
Instance BtR5 `{BD 5} : RD 5 := {}.
Instance LtR5 `{LD 5} : TD 5 := {}.
Instance RtR5 `{RD 5} : TD 5 := {}.
Instance Ttb5 `{TD 5} : BD (S 5) := {}.

Instance BtL6 `{BD 6} : LD 6 := {}.
Instance BtR6 `{BD 6} : RD 6 := {}.
Instance LtR6 `{LD 6} : TD 6 := {}.
Instance RtR6 `{RD 6} : TD 6 := {}.
Instance Ttb6 `{TD 6} : BD (S 6) := {}.

Instance BtL7 `{BD 7} : LD 7 := {}.
Instance BtR7 `{BD 7} : RD 7 := {}.
Instance LtR7 `{LD 7} : TD 7 := {}.
Instance RtR7 `{RD 7} : TD 7 := {}.
Instance Ttb7 `{TD 7} : BD (S 7) := {}.

Instance BtL8 `{BD 8} : LD 8 := {}.
Instance BtR8 `{BD 8} : RD 8 := {}.
Instance LtR8 `{LD 8} : TD 8 := {}.
Instance RtR8 `{RD 8} : TD 8 := {}.
Instance Ttb8 `{TD 8} : BD (S 8) := {}.

Instance BtL9 `{BD 9} : LD 9 := {}.
Instance BtR9 `{BD 9} : RD 9 := {}.
Instance LtR9 `{LD 9} : TD 9 := {}.
Instance RtR9 `{RD 9} : TD 9 := {}.
Instance Ttb9 `{TD 9} : BD (S 9) := {}.

Instance BtL10 `{BD 10} : LD 10 := {}.
Instance BtR10 `{BD 10} : RD 10 := {}.
Instance LtR10 `{LD 10} : TD 10 := {}.
Instance RtR10 `{RD 10} : TD 10 := {}.
Instance Ttb10 `{TD 10} : BD (S 10) := {}.

Instance BtL11 `{BD 11} : LD 11 := {}.
Instance BtR11 `{BD 11} : RD 11 := {}.
Instance LtR11 `{LD 11} : TD 11 := {}.
Instance RtR11 `{RD 11} : TD 11 := {}.
Instance Ttb11 `{TD 11} : BD (S 11) := {}.

Instance BtL12 `{BD 12} : LD 12 := {}.
Instance BtR12 `{BD 12} : RD 12 := {}.
Instance LtR12 `{LD 12} : TD 12 := {}.
Instance RtR12 `{RD 12} : TD 12 := {}.
Instance Ttb12 `{TD 12} : BD (S 12) := {}.

Instance BtL13 `{BD 13} : LD 13 := {}.
Instance BtR13 `{BD 13} : RD 13 := {}.
Instance LtR13 `{LD 13} : TD 13 := {}.
Instance RtR13 `{RD 13} : TD 13 := {}.
Instance Ttb13 `{TD 13} : BD (S 13) := {}.

Instance BtL14 `{BD 14} : LD 14 := {}.
Instance BtR14 `{BD 14} : RD 14 := {}.
Instance LtR14 `{LD 14} : TD 14 := {}.
Instance RtR14 `{RD 14} : TD 14 := {}.
Instance Ttb14 `{TD 14} : BD (S 14) := {}.

Instance BtL15 `{BD 15} : LD 15 := {}.
Instance BtR15 `{BD 15} : RD 15 := {}.
Instance LtR15 `{LD 15} : TD 15 := {}.
Instance RtR15 `{RD 15} : TD 15 := {}.
Instance Ttb15 `{TD 15} : BD (S 15) := {}.

Instance BtL16 `{BD 16} : LD 16 := {}.
Instance BtR16 `{BD 16} : RD 16 := {}.
Instance LtR16 `{LD 16} : TD 16 := {}.
Instance RtR16 `{RD 16} : TD 16 := {}.
Instance Ttb16 `{TD 16} : BD (S 16) := {}.

Instance BtL17 `{BD 17} : LD 17 := {}.
Instance BtR17 `{BD 17} : RD 17 := {}.
Instance LtR17 `{LD 17} : TD 17 := {}.
Instance RtR17 `{RD 17} : TD 17 := {}.
Instance Ttb17 `{TD 17} : BD (S 17) := {}.

Instance BtL18 `{BD 18} : LD 18 := {}.
Instance BtR18 `{BD 18} : RD 18 := {}.
Instance LtR18 `{LD 18} : TD 18 := {}.
Instance RtR18 `{RD 18} : TD 18 := {}.
Instance Ttb18 `{TD 18} : BD (S 18) := {}.

Instance BtL19 `{BD 19} : LD 19 := {}.
Instance BtR19 `{BD 19} : RD 19 := {}.
Instance LtR19 `{LD 19} : TD 19 := {}.
Instance RtR19 `{RD 19} : TD 19 := {}.
Instance Ttb19 `{TD 19} : BD (S 19) := {}.

Instance BtL20 `{BD 20} : LD 20 := {}.
Instance BtR20 `{BD 20} : RD 20 := {}.
Instance LtR20 `{LD 20} : TD 20 := {}.
Instance RtR20 `{RD 20} : TD 20 := {}.
Instance Ttb20 `{TD 20} : BD (S 20) := {}.

Instance BtL21 `{BD 21} : LD 21 := {}.
Instance BtR21 `{BD 21} : RD 21 := {}.
Instance LtR21 `{LD 21} : TD 21 := {}.
Instance RtR21 `{RD 21} : TD 21 := {}.
Instance Ttb21 `{TD 21} : BD (S 21) := {}.

Instance BtL22 `{BD 22} : LD 22 := {}.
Instance BtR22 `{BD 22} : RD 22 := {}.
Instance LtR22 `{LD 22} : TD 22 := {}.
Instance RtR22 `{RD 22} : TD 22 := {}.
Instance Ttb22 `{TD 22} : BD (S 22) := {}.

Instance BtL23 `{BD 23} : LD 23 := {}.
Instance BtR23 `{BD 23} : RD 23 := {}.
Instance LtR23 `{LD 23} : TD 23 := {}.
Instance RtR23 `{RD 23} : TD 23 := {}.
Instance Ttb23 `{TD 23} : BD (S 23) := {}.

Instance BtL24 `{BD 24} : LD 24 := {}.
Instance BtR24 `{BD 24} : RD 24 := {}.
Instance LtR24 `{LD 24} : TD 24 := {}.
Instance RtR24 `{RD 24} : TD 24 := {}.
Instance Ttb24 `{TD 24} : BD (S 24) := {}.

Instance BtL25 `{BD 25} : LD 25 := {}.
Instance BtR25 `{BD 25} : RD 25 := {}.
Instance LtR25 `{LD 25} : TD 25 := {}.
Instance RtR25 `{RD 25} : TD 25 := {}.
Instance Ttb25 `{TD 25} : BD (S 25) := {}.

Instance BtL26 `{BD 26} : LD 26 := {}.
Instance BtR26 `{BD 26} : RD 26 := {}.
Instance LtR26 `{LD 26} : TD 26 := {}.
Instance RtR26 `{RD 26} : TD 26 := {}.
Instance Ttb26 `{TD 26} : BD (S 26) := {}.

Instance BtL27 `{BD 27} : LD 27 := {}.
Instance BtR27 `{BD 27} : RD 27 := {}.
Instance LtR27 `{LD 27} : TD 27 := {}.
Instance RtR27 `{RD 27} : TD 27 := {}.
Instance Ttb27 `{TD 27} : BD (S 27) := {}.

Instance BtL28 `{BD 28} : LD 28 := {}.
Instance BtR28 `{BD 28} : RD 28 := {}.
Instance LtR28 `{LD 28} : TD 28 := {}.
Instance RtR28 `{RD 28} : TD 28 := {}.
Instance Ttb28 `{TD 28} : BD (S 28) := {}.

Instance BtL29 `{BD 29} : LD 29 := {}.
Instance BtR29 `{BD 29} : RD 29 := {}.
Instance LtR29 `{LD 29} : TD 29 := {}.
Instance RtR29 `{RD 29} : TD 29 := {}.
Instance Ttb29 `{TD 29} : BD (S 29) := {}.

Instance BtL30 `{BD 30} : LD 30 := {}.
Instance BtR30 `{BD 30} : RD 30 := {}.
Instance LtR30 `{LD 30} : TD 30 := {}.
Instance RtR30 `{RD 30} : TD 30 := {}.
Instance Ttb30 `{TD 30} : BD (S 30) := {}.

Instance BtL31 `{BD 31} : LD 31 := {}.
Instance BtR31 `{BD 31} : RD 31 := {}.
Instance LtR31 `{LD 31} : TD 31 := {}.
Instance RtR31 `{RD 31} : TD 31 := {}.
Instance Ttb31 `{TD 31} : BD (S 31) := {}.

Instance BtL32 `{BD 32} : LD 32 := {}.
Instance BtR32 `{BD 32} : RD 32 := {}.
Instance LtR32 `{LD 32} : TD 32 := {}.
Instance RtR32 `{RD 32} : TD 32 := {}.
Instance Ttb32 `{TD 32} : BD (S 32) := {}.

Instance BtL33 `{BD 33} : LD 33 := {}.
Instance BtR33 `{BD 33} : RD 33 := {}.
Instance LtR33 `{LD 33} : TD 33 := {}.
Instance RtR33 `{RD 33} : TD 33 := {}.
Instance Ttb33 `{TD 33} : BD (S 33) := {}.

Instance BtL34 `{BD 34} : LD 34 := {}.
Instance BtR34 `{BD 34} : RD 34 := {}.
Instance LtR34 `{LD 34} : TD 34 := {}.
Instance RtR34 `{RD 34} : TD 34 := {}.
Instance Ttb34 `{TD 34} : BD (S 34) := {}.

Instance BtL35 `{BD 35} : LD 35 := {}.
Instance BtR35 `{BD 35} : RD 35 := {}.
Instance LtR35 `{LD 35} : TD 35 := {}.
Instance RtR35 `{RD 35} : TD 35 := {}.
Instance Ttb35 `{TD 35} : BD (S 35) := {}.

Instance BtL36 `{BD 36} : LD 36 := {}.
Instance BtR36 `{BD 36} : RD 36 := {}.
Instance LtR36 `{LD 36} : TD 36 := {}.
Instance RtR36 `{RD 36} : TD 36 := {}.
Instance Ttb36 `{TD 36} : BD (S 36) := {}.

Instance BtL37 `{BD 37} : LD 37 := {}.
Instance BtR37 `{BD 37} : RD 37 := {}.
Instance LtR37 `{LD 37} : TD 37 := {}.
Instance RtR37 `{RD 37} : TD 37 := {}.
Instance Ttb37 `{TD 37} : BD (S 37) := {}.

Instance BtL38 `{BD 38} : LD 38 := {}.
Instance BtR38 `{BD 38} : RD 38 := {}.
Instance LtR38 `{LD 38} : TD 38 := {}.
Instance RtR38 `{RD 38} : TD 38 := {}.
Instance Ttb38 `{TD 38} : BD (S 38) := {}.

Instance BtL39 `{BD 39} : LD 39 := {}.
Instance BtR39 `{BD 39} : RD 39 := {}.
Instance LtR39 `{LD 39} : TD 39 := {}.
Instance RtR39 `{RD 39} : TD 39 := {}.
Instance Ttb39 `{TD 39} : BD (S 39) := {}.

Instance BtL40 `{BD 40} : LD 40 := {}.
Instance BtR40 `{BD 40} : RD 40 := {}.
Instance LtR40 `{LD 40} : TD 40 := {}.
Instance RtR40 `{RD 40} : TD 40 := {}.
Instance Ttb40 `{TD 40} : BD (S 40) := {}.

Instance BtL41 `{BD 41} : LD 41 := {}.
Instance BtR41 `{BD 41} : RD 41 := {}.
Instance LtR41 `{LD 41} : TD 41 := {}.
Instance RtR41 `{RD 41} : TD 41 := {}.
Instance Ttb41 `{TD 41} : BD (S 41) := {}.

Instance BtL42 `{BD 42} : LD 42 := {}.
Instance BtR42 `{BD 42} : RD 42 := {}.
Instance LtR42 `{LD 42} : TD 42 := {}.
Instance RtR42 `{RD 42} : TD 42 := {}.
Instance Ttb42 `{TD 42} : BD (S 42) := {}.

Instance BtL43 `{BD 43} : LD 43 := {}.
Instance BtR43 `{BD 43} : RD 43 := {}.
Instance LtR43 `{LD 43} : TD 43 := {}.
Instance RtR43 `{RD 43} : TD 43 := {}.
Instance Ttb43 `{TD 43} : BD (S 43) := {}.

Instance BtL44 `{BD 44} : LD 44 := {}.
Instance BtR44 `{BD 44} : RD 44 := {}.
Instance LtR44 `{LD 44} : TD 44 := {}.
Instance RtR44 `{RD 44} : TD 44 := {}.
Instance Ttb44 `{TD 44} : BD (S 44) := {}.

Instance BtL45 `{BD 45} : LD 45 := {}.
Instance BtR45 `{BD 45} : RD 45 := {}.
Instance LtR45 `{LD 45} : TD 45 := {}.
Instance RtR45 `{RD 45} : TD 45 := {}.
Instance Ttb45 `{TD 45} : BD (S 45) := {}.

Instance BtL46 `{BD 46} : LD 46 := {}.
Instance BtR46 `{BD 46} : RD 46 := {}.
Instance LtR46 `{LD 46} : TD 46 := {}.
Instance RtR46 `{RD 46} : TD 46 := {}.
Instance Ttb46 `{TD 46} : BD (S 46) := {}.

Instance BtL47 `{BD 47} : LD 47 := {}.
Instance BtR47 `{BD 47} : RD 47 := {}.
Instance LtR47 `{LD 47} : TD 47 := {}.
Instance RtR47 `{RD 47} : TD 47 := {}.
Instance Ttb47 `{TD 47} : BD (S 47) := {}.

Instance BtL48 `{BD 48} : LD 48 := {}.
Instance BtR48 `{BD 48} : RD 48 := {}.
Instance LtR48 `{LD 48} : TD 48 := {}.
Instance RtR48 `{RD 48} : TD 48 := {}.
Instance Ttb48 `{TD 48} : BD (S 48) := {}.

Instance BtL49 `{BD 49} : LD 49 := {}.
Instance BtR49 `{BD 49} : RD 49 := {}.
Instance LtR49 `{LD 49} : TD 49 := {}.
Instance RtR49 `{RD 49} : TD 49 := {}.
Instance Ttb49 `{TD 49} : BD (S 49) := {}.

Instance BtL50 `{BD 50} : LD 50 := {}.
Instance BtR50 `{BD 50} : RD 50 := {}.
Instance LtR50 `{LD 50} : TD 50 := {}.
Instance RtR50 `{RD 50} : TD 50 := {}.
Instance Ttb50 `{TD 50} : BD (S 50) := {}.

Instance BtL51 `{BD 51} : LD 51 := {}.
Instance BtR51 `{BD 51} : RD 51 := {}.
Instance LtR51 `{LD 51} : TD 51 := {}.
Instance RtR51 `{RD 51} : TD 51 := {}.
Instance Ttb51 `{TD 51} : BD (S 51) := {}.

Instance BtL52 `{BD 52} : LD 52 := {}.
Instance BtR52 `{BD 52} : RD 52 := {}.
Instance LtR52 `{LD 52} : TD 52 := {}.
Instance RtR52 `{RD 52} : TD 52 := {}.
Instance Ttb52 `{TD 52} : BD (S 52) := {}.

Instance BtL53 `{BD 53} : LD 53 := {}.
Instance BtR53 `{BD 53} : RD 53 := {}.
Instance LtR53 `{LD 53} : TD 53 := {}.
Instance RtR53 `{RD 53} : TD 53 := {}.
Instance Ttb53 `{TD 53} : BD (S 53) := {}.

Instance BtL54 `{BD 54} : LD 54 := {}.
Instance BtR54 `{BD 54} : RD 54 := {}.
Instance LtR54 `{LD 54} : TD 54 := {}.
Instance RtR54 `{RD 54} : TD 54 := {}.
Instance Ttb54 `{TD 54} : BD (S 54) := {}.

Instance BtL55 `{BD 55} : LD 55 := {}.
Instance BtR55 `{BD 55} : RD 55 := {}.
Instance LtR55 `{LD 55} : TD 55 := {}.
Instance RtR55 `{RD 55} : TD 55 := {}.
Instance Ttb55 `{TD 55} : BD (S 55) := {}.

Instance BtL56 `{BD 56} : LD 56 := {}.
Instance BtR56 `{BD 56} : RD 56 := {}.
Instance LtR56 `{LD 56} : TD 56 := {}.
Instance RtR56 `{RD 56} : TD 56 := {}.
Instance Ttb56 `{TD 56} : BD (S 56) := {}.

Instance BtL57 `{BD 57} : LD 57 := {}.
Instance BtR57 `{BD 57} : RD 57 := {}.
Instance LtR57 `{LD 57} : TD 57 := {}.
Instance RtR57 `{RD 57} : TD 57 := {}.
Instance Ttb57 `{TD 57} : BD (S 57) := {}.

Instance BtL58 `{BD 58} : LD 58 := {}.
Instance BtR58 `{BD 58} : RD 58 := {}.
Instance LtR58 `{LD 58} : TD 58 := {}.
Instance RtR58 `{RD 58} : TD 58 := {}.
Instance Ttb58 `{TD 58} : BD (S 58) := {}.

Instance BtL59 `{BD 59} : LD 59 := {}.
Instance BtR59 `{BD 59} : RD 59 := {}.
Instance LtR59 `{LD 59} : TD 59 := {}.
Instance RtR59 `{RD 59} : TD 59 := {}.
Instance Ttb59 `{TD 59} : BD (S 59) := {}.

Instance BtL60 `{BD 60} : LD 60 := {}.
Instance BtR60 `{BD 60} : RD 60 := {}.
Instance LtR60 `{LD 60} : TD 60 := {}.
Instance RtR60 `{RD 60} : TD 60 := {}.
Instance Ttb60 `{TD 60} : BD (S 60) := {}.

Instance BtL61 `{BD 61} : LD 61 := {}.
Instance BtR61 `{BD 61} : RD 61 := {}.
Instance LtR61 `{LD 61} : TD 61 := {}.
Instance RtR61 `{RD 61} : TD 61 := {}.
Instance Ttb61 `{TD 61} : BD (S 61) := {}.

Instance BtL62 `{BD 62} : LD 62 := {}.
Instance BtR62 `{BD 62} : RD 62 := {}.
Instance LtR62 `{LD 62} : TD 62 := {}.
Instance RtR62 `{RD 62} : TD 62 := {}.
Instance Ttb62 `{TD 62} : BD (S 62) := {}.

Instance BtL63 `{BD 63} : LD 63 := {}.
Instance BtR63 `{BD 63} : RD 63 := {}.
Instance LtR63 `{LD 63} : TD 63 := {}.
Instance RtR63 `{RD 63} : TD 63 := {}.
Instance Ttb63 `{TD 63} : BD (S 63) := {}.

Instance BtL64 `{BD 64} : LD 64 := {}.
Instance BtR64 `{BD 64} : RD 64 := {}.
Instance LtR64 `{LD 64} : TD 64 := {}.
Instance RtR64 `{RD 64} : TD 64 := {}.
Instance Ttb64 `{TD 64} : BD (S 64) := {}.

Instance BtL65 `{BD 65} : LD 65 := {}.
Instance BtR65 `{BD 65} : RD 65 := {}.
Instance LtR65 `{LD 65} : TD 65 := {}.
Instance RtR65 `{RD 65} : TD 65 := {}.
Instance Ttb65 `{TD 65} : BD (S 65) := {}.

Instance BtL66 `{BD 66} : LD 66 := {}.
Instance BtR66 `{BD 66} : RD 66 := {}.
Instance LtR66 `{LD 66} : TD 66 := {}.
Instance RtR66 `{RD 66} : TD 66 := {}.
Instance Ttb66 `{TD 66} : BD (S 66) := {}.

Instance BtL67 `{BD 67} : LD 67 := {}.
Instance BtR67 `{BD 67} : RD 67 := {}.
Instance LtR67 `{LD 67} : TD 67 := {}.
Instance RtR67 `{RD 67} : TD 67 := {}.
Instance Ttb67 `{TD 67} : BD (S 67) := {}.

Instance BtL68 `{BD 68} : LD 68 := {}.
Instance BtR68 `{BD 68} : RD 68 := {}.
Instance LtR68 `{LD 68} : TD 68 := {}.
Instance RtR68 `{RD 68} : TD 68 := {}.
Instance Ttb68 `{TD 68} : BD (S 68) := {}.

Instance BtL69 `{BD 69} : LD 69 := {}.
Instance BtR69 `{BD 69} : RD 69 := {}.
Instance LtR69 `{LD 69} : TD 69 := {}.
Instance RtR69 `{RD 69} : TD 69 := {}.
Instance Ttb69 `{TD 69} : BD (S 69) := {}.

Instance BtL70 `{BD 70} : LD 70 := {}.
Instance BtR70 `{BD 70} : RD 70 := {}.
Instance LtR70 `{LD 70} : TD 70 := {}.
Instance RtR70 `{RD 70} : TD 70 := {}.
Instance Ttb70 `{TD 70} : BD (S 70) := {}.

Instance BtL71 `{BD 71} : LD 71 := {}.
Instance BtR71 `{BD 71} : RD 71 := {}.
Instance LtR71 `{LD 71} : TD 71 := {}.
Instance RtR71 `{RD 71} : TD 71 := {}.
Instance Ttb71 `{TD 71} : BD (S 71) := {}.

Instance BtL72 `{BD 72} : LD 72 := {}.
Instance BtR72 `{BD 72} : RD 72 := {}.
Instance LtR72 `{LD 72} : TD 72 := {}.
Instance RtR72 `{RD 72} : TD 72 := {}.
Instance Ttb72 `{TD 72} : BD (S 72) := {}.

Instance BtL73 `{BD 73} : LD 73 := {}.
Instance BtR73 `{BD 73} : RD 73 := {}.
Instance LtR73 `{LD 73} : TD 73 := {}.
Instance RtR73 `{RD 73} : TD 73 := {}.
Instance Ttb73 `{TD 73} : BD (S 73) := {}.

Instance BtL74 `{BD 74} : LD 74 := {}.
Instance BtR74 `{BD 74} : RD 74 := {}.
Instance LtR74 `{LD 74} : TD 74 := {}.
Instance RtR74 `{RD 74} : TD 74 := {}.
Instance Ttb74 `{TD 74} : BD (S 74) := {}.

Instance BtL75 `{BD 75} : LD 75 := {}.
Instance BtR75 `{BD 75} : RD 75 := {}.
Instance LtR75 `{LD 75} : TD 75 := {}.
Instance RtR75 `{RD 75} : TD 75 := {}.
Instance Ttb75 `{TD 75} : BD (S 75) := {}.

Instance BtL76 `{BD 76} : LD 76 := {}.
Instance BtR76 `{BD 76} : RD 76 := {}.
Instance LtR76 `{LD 76} : TD 76 := {}.
Instance RtR76 `{RD 76} : TD 76 := {}.
Instance Ttb76 `{TD 76} : BD (S 76) := {}.

Instance BtL77 `{BD 77} : LD 77 := {}.
Instance BtR77 `{BD 77} : RD 77 := {}.
Instance LtR77 `{LD 77} : TD 77 := {}.
Instance RtR77 `{RD 77} : TD 77 := {}.
Instance Ttb77 `{TD 77} : BD (S 77) := {}.

Instance BtL78 `{BD 78} : LD 78 := {}.
Instance BtR78 `{BD 78} : RD 78 := {}.
Instance LtR78 `{LD 78} : TD 78 := {}.
Instance RtR78 `{RD 78} : TD 78 := {}.
Instance Ttb78 `{TD 78} : BD (S 78) := {}.

Instance BtL79 `{BD 79} : LD 79 := {}.
Instance BtR79 `{BD 79} : RD 79 := {}.
Instance LtR79 `{LD 79} : TD 79 := {}.
Instance RtR79 `{RD 79} : TD 79 := {}.
Instance Ttb79 `{TD 79} : BD (S 79) := {}.

Instance BtL80 `{BD 80} : LD 80 := {}.
Instance BtR80 `{BD 80} : RD 80 := {}.
Instance LtR80 `{LD 80} : TD 80 := {}.
Instance RtR80 `{RD 80} : TD 80 := {}.
Instance Ttb80 `{TD 80} : BD (S 80) := {}.

Instance BtL81 `{BD 81} : LD 81 := {}.
Instance BtR81 `{BD 81} : RD 81 := {}.
Instance LtR81 `{LD 81} : TD 81 := {}.
Instance RtR81 `{RD 81} : TD 81 := {}.
Instance Ttb81 `{TD 81} : BD (S 81) := {}.

Instance BtL82 `{BD 82} : LD 82 := {}.
Instance BtR82 `{BD 82} : RD 82 := {}.
Instance LtR82 `{LD 82} : TD 82 := {}.
Instance RtR82 `{RD 82} : TD 82 := {}.
Instance Ttb82 `{TD 82} : BD (S 82) := {}.

Instance BtL83 `{BD 83} : LD 83 := {}.
Instance BtR83 `{BD 83} : RD 83 := {}.
Instance LtR83 `{LD 83} : TD 83 := {}.
Instance RtR83 `{RD 83} : TD 83 := {}.
Instance Ttb83 `{TD 83} : BD (S 83) := {}.

Instance BtL84 `{BD 84} : LD 84 := {}.
Instance BtR84 `{BD 84} : RD 84 := {}.
Instance LtR84 `{LD 84} : TD 84 := {}.
Instance RtR84 `{RD 84} : TD 84 := {}.
Instance Ttb84 `{TD 84} : BD (S 84) := {}.

Instance BtL85 `{BD 85} : LD 85 := {}.
Instance BtR85 `{BD 85} : RD 85 := {}.
Instance LtR85 `{LD 85} : TD 85 := {}.
Instance RtR85 `{RD 85} : TD 85 := {}.
Instance Ttb85 `{TD 85} : BD (S 85) := {}.

Instance BtL86 `{BD 86} : LD 86 := {}.
Instance BtR86 `{BD 86} : RD 86 := {}.
Instance LtR86 `{LD 86} : TD 86 := {}.
Instance RtR86 `{RD 86} : TD 86 := {}.
Instance Ttb86 `{TD 86} : BD (S 86) := {}.

Instance BtL87 `{BD 87} : LD 87 := {}.
Instance BtR87 `{BD 87} : RD 87 := {}.
Instance LtR87 `{LD 87} : TD 87 := {}.
Instance RtR87 `{RD 87} : TD 87 := {}.
Instance Ttb87 `{TD 87} : BD (S 87) := {}.

Instance BtL88 `{BD 88} : LD 88 := {}.
Instance BtR88 `{BD 88} : RD 88 := {}.
Instance LtR88 `{LD 88} : TD 88 := {}.
Instance RtR88 `{RD 88} : TD 88 := {}.
Instance Ttb88 `{TD 88} : BD (S 88) := {}.

Instance BtL89 `{BD 89} : LD 89 := {}.
Instance BtR89 `{BD 89} : RD 89 := {}.
Instance LtR89 `{LD 89} : TD 89 := {}.
Instance RtR89 `{RD 89} : TD 89 := {}.
Instance Ttb89 `{TD 89} : BD (S 89) := {}.

Instance BtL90 `{BD 90} : LD 90 := {}.
Instance BtR90 `{BD 90} : RD 90 := {}.
Instance LtR90 `{LD 90} : TD 90 := {}.
Instance RtR90 `{RD 90} : TD 90 := {}.
Instance Ttb90 `{TD 90} : BD (S 90) := {}.

Instance BtL91 `{BD 91} : LD 91 := {}.
Instance BtR91 `{BD 91} : RD 91 := {}.
Instance LtR91 `{LD 91} : TD 91 := {}.
Instance RtR91 `{RD 91} : TD 91 := {}.
Instance Ttb91 `{TD 91} : BD (S 91) := {}.

Instance BtL92 `{BD 92} : LD 92 := {}.
Instance BtR92 `{BD 92} : RD 92 := {}.
Instance LtR92 `{LD 92} : TD 92 := {}.
Instance RtR92 `{RD 92} : TD 92 := {}.
Instance Ttb92 `{TD 92} : BD (S 92) := {}.

Instance BtL93 `{BD 93} : LD 93 := {}.
Instance BtR93 `{BD 93} : RD 93 := {}.
Instance LtR93 `{LD 93} : TD 93 := {}.
Instance RtR93 `{RD 93} : TD 93 := {}.
Instance Ttb93 `{TD 93} : BD (S 93) := {}.

Instance BtL94 `{BD 94} : LD 94 := {}.
Instance BtR94 `{BD 94} : RD 94 := {}.
Instance LtR94 `{LD 94} : TD 94 := {}.
Instance RtR94 `{RD 94} : TD 94 := {}.
Instance Ttb94 `{TD 94} : BD (S 94) := {}.

Instance BtL95 `{BD 95} : LD 95 := {}.
Instance BtR95 `{BD 95} : RD 95 := {}.
Instance LtR95 `{LD 95} : TD 95 := {}.
Instance RtR95 `{RD 95} : TD 95 := {}.
Instance Ttb95 `{TD 95} : BD (S 95) := {}.

Instance BtL96 `{BD 96} : LD 96 := {}.
Instance BtR96 `{BD 96} : RD 96 := {}.
Instance LtR96 `{LD 96} : TD 96 := {}.
Instance RtR96 `{RD 96} : TD 96 := {}.
Instance Ttb96 `{TD 96} : BD (S 96) := {}.

Instance BtL97 `{BD 97} : LD 97 := {}.
Instance BtR97 `{BD 97} : RD 97 := {}.
Instance LtR97 `{LD 97} : TD 97 := {}.
Instance RtR97 `{RD 97} : TD 97 := {}.
Instance Ttb97 `{TD 97} : BD (S 97) := {}.

Instance BtL98 `{BD 98} : LD 98 := {}.
Instance BtR98 `{BD 98} : RD 98 := {}.
Instance LtR98 `{LD 98} : TD 98 := {}.
Instance RtR98 `{RD 98} : TD 98 := {}.
Instance Ttb98 `{TD 98} : BD (S 98) := {}.

Instance BtL99 `{BD 99} : LD 99 := {}.
Instance BtR99 `{BD 99} : RD 99 := {}.
Instance LtR99 `{LD 99} : TD 99 := {}.
Instance RtR99 `{RD 99} : TD 99 := {}.
Instance Ttb99 `{TD 99} : BD (S 99) := {}.

Instance BtL100 `{BD 100} : LD 100 := {}.
Instance BtR100 `{BD 100} : RD 100 := {}.
Instance LtR100 `{LD 100} : TD 100 := {}.
Instance RtR100 `{RD 100} : TD 100 := {}.
Instance Ttb100 `{TD 100} : BD (S 100) := {}.

Instance BtL101 `{BD 101} : LD 101 := {}.
Instance BtR101 `{BD 101} : RD 101 := {}.
Instance LtR101 `{LD 101} : TD 101 := {}.
Instance RtR101 `{RD 101} : TD 101 := {}.
Instance Ttb101 `{TD 101} : BD (S 101) := {}.

Instance BtL102 `{BD 102} : LD 102 := {}.
Instance BtR102 `{BD 102} : RD 102 := {}.
Instance LtR102 `{LD 102} : TD 102 := {}.
Instance RtR102 `{RD 102} : TD 102 := {}.
Instance Ttb102 `{TD 102} : BD (S 102) := {}.

Instance BtL103 `{BD 103} : LD 103 := {}.
Instance BtR103 `{BD 103} : RD 103 := {}.
Instance LtR103 `{LD 103} : TD 103 := {}.
Instance RtR103 `{RD 103} : TD 103 := {}.
Instance Ttb103 `{TD 103} : BD (S 103) := {}.

Instance BtL104 `{BD 104} : LD 104 := {}.
Instance BtR104 `{BD 104} : RD 104 := {}.
Instance LtR104 `{LD 104} : TD 104 := {}.
Instance RtR104 `{RD 104} : TD 104 := {}.
Instance Ttb104 `{TD 104} : BD (S 104) := {}.

Instance BtL105 `{BD 105} : LD 105 := {}.
Instance BtR105 `{BD 105} : RD 105 := {}.
Instance LtR105 `{LD 105} : TD 105 := {}.
Instance RtR105 `{RD 105} : TD 105 := {}.
Instance Ttb105 `{TD 105} : BD (S 105) := {}.

Instance BtL106 `{BD 106} : LD 106 := {}.
Instance BtR106 `{BD 106} : RD 106 := {}.
Instance LtR106 `{LD 106} : TD 106 := {}.
Instance RtR106 `{RD 106} : TD 106 := {}.
Instance Ttb106 `{TD 106} : BD (S 106) := {}.

Instance BtL107 `{BD 107} : LD 107 := {}.
Instance BtR107 `{BD 107} : RD 107 := {}.
Instance LtR107 `{LD 107} : TD 107 := {}.
Instance RtR107 `{RD 107} : TD 107 := {}.
Instance Ttb107 `{TD 107} : BD (S 107) := {}.

Instance BtL108 `{BD 108} : LD 108 := {}.
Instance BtR108 `{BD 108} : RD 108 := {}.
Instance LtR108 `{LD 108} : TD 108 := {}.
Instance RtR108 `{RD 108} : TD 108 := {}.
Instance Ttb108 `{TD 108} : BD (S 108) := {}.

Instance BtL109 `{BD 109} : LD 109 := {}.
Instance BtR109 `{BD 109} : RD 109 := {}.
Instance LtR109 `{LD 109} : TD 109 := {}.
Instance RtR109 `{RD 109} : TD 109 := {}.
Instance Ttb109 `{TD 109} : BD (S 109) := {}.

Instance BtL110 `{BD 110} : LD 110 := {}.
Instance BtR110 `{BD 110} : RD 110 := {}.
Instance LtR110 `{LD 110} : TD 110 := {}.
Instance RtR110 `{RD 110} : TD 110 := {}.
Instance Ttb110 `{TD 110} : BD (S 110) := {}.

Instance BtL111 `{BD 111} : LD 111 := {}.
Instance BtR111 `{BD 111} : RD 111 := {}.
Instance LtR111 `{LD 111} : TD 111 := {}.
Instance RtR111 `{RD 111} : TD 111 := {}.
Instance Ttb111 `{TD 111} : BD (S 111) := {}.

Instance BtL112 `{BD 112} : LD 112 := {}.
Instance BtR112 `{BD 112} : RD 112 := {}.
Instance LtR112 `{LD 112} : TD 112 := {}.
Instance RtR112 `{RD 112} : TD 112 := {}.
Instance Ttb112 `{TD 112} : BD (S 112) := {}.

Instance BtL113 `{BD 113} : LD 113 := {}.
Instance BtR113 `{BD 113} : RD 113 := {}.
Instance LtR113 `{LD 113} : TD 113 := {}.
Instance RtR113 `{RD 113} : TD 113 := {}.
Instance Ttb113 `{TD 113} : BD (S 113) := {}.

Instance BtL114 `{BD 114} : LD 114 := {}.
Instance BtR114 `{BD 114} : RD 114 := {}.
Instance LtR114 `{LD 114} : TD 114 := {}.
Instance RtR114 `{RD 114} : TD 114 := {}.
Instance Ttb114 `{TD 114} : BD (S 114) := {}.

Instance BtL115 `{BD 115} : LD 115 := {}.
Instance BtR115 `{BD 115} : RD 115 := {}.
Instance LtR115 `{LD 115} : TD 115 := {}.
Instance RtR115 `{RD 115} : TD 115 := {}.
Instance Ttb115 `{TD 115} : BD (S 115) := {}.

Instance BtL116 `{BD 116} : LD 116 := {}.
Instance BtR116 `{BD 116} : RD 116 := {}.
Instance LtR116 `{LD 116} : TD 116 := {}.
Instance RtR116 `{RD 116} : TD 116 := {}.
Instance Ttb116 `{TD 116} : BD (S 116) := {}.

Instance BtL117 `{BD 117} : LD 117 := {}.
Instance BtR117 `{BD 117} : RD 117 := {}.
Instance LtR117 `{LD 117} : TD 117 := {}.
Instance RtR117 `{RD 117} : TD 117 := {}.
Instance Ttb117 `{TD 117} : BD (S 117) := {}.

Instance BtL118 `{BD 118} : LD 118 := {}.
Instance BtR118 `{BD 118} : RD 118 := {}.
Instance LtR118 `{LD 118} : TD 118 := {}.
Instance RtR118 `{RD 118} : TD 118 := {}.
Instance Ttb118 `{TD 118} : BD (S 118) := {}.

Instance BtL119 `{BD 119} : LD 119 := {}.
Instance BtR119 `{BD 119} : RD 119 := {}.
Instance LtR119 `{LD 119} : TD 119 := {}.
Instance RtR119 `{RD 119} : TD 119 := {}.
Instance Ttb119 `{TD 119} : BD (S 119) := {}.

Instance BtL120 `{BD 120} : LD 120 := {}.
Instance BtR120 `{BD 120} : RD 120 := {}.
Instance LtR120 `{LD 120} : TD 120 := {}.
Instance RtR120 `{RD 120} : TD 120 := {}.
Instance Ttb120 `{TD 120} : BD (S 120) := {}.

Instance BtL121 `{BD 121} : LD 121 := {}.
Instance BtR121 `{BD 121} : RD 121 := {}.
Instance LtR121 `{LD 121} : TD 121 := {}.
Instance RtR121 `{RD 121} : TD 121 := {}.
Instance Ttb121 `{TD 121} : BD (S 121) := {}.

Instance BtL122 `{BD 122} : LD 122 := {}.
Instance BtR122 `{BD 122} : RD 122 := {}.
Instance LtR122 `{LD 122} : TD 122 := {}.
Instance RtR122 `{RD 122} : TD 122 := {}.
Instance Ttb122 `{TD 122} : BD (S 122) := {}.

Instance BtL123 `{BD 123} : LD 123 := {}.
Instance BtR123 `{BD 123} : RD 123 := {}.
Instance LtR123 `{LD 123} : TD 123 := {}.
Instance RtR123 `{RD 123} : TD 123 := {}.
Instance Ttb123 `{TD 123} : BD (S 123) := {}.

Instance BtL124 `{BD 124} : LD 124 := {}.
Instance BtR124 `{BD 124} : RD 124 := {}.
Instance LtR124 `{LD 124} : TD 124 := {}.
Instance RtR124 `{RD 124} : TD 124 := {}.
Instance Ttb124 `{TD 124} : BD (S 124) := {}.

Instance BtL125 `{BD 125} : LD 125 := {}.
Instance BtR125 `{BD 125} : RD 125 := {}.
Instance LtR125 `{LD 125} : TD 125 := {}.
Instance RtR125 `{RD 125} : TD 125 := {}.
Instance Ttb125 `{TD 125} : BD (S 125) := {}.

Instance BtL126 `{BD 126} : LD 126 := {}.
Instance BtR126 `{BD 126} : RD 126 := {}.
Instance LtR126 `{LD 126} : TD 126 := {}.
Instance RtR126 `{RD 126} : TD 126 := {}.
Instance Ttb126 `{TD 126} : BD (S 126) := {}.

Instance BtL127 `{BD 127} : LD 127 := {}.
Instance BtR127 `{BD 127} : RD 127 := {}.
Instance LtR127 `{LD 127} : TD 127 := {}.
Instance RtR127 `{RD 127} : TD 127 := {}.
Instance Ttb127 `{TD 127} : BD (S 127) := {}.

Instance BtL128 `{BD 128} : LD 128 := {}.
Instance BtR128 `{BD 128} : RD 128 := {}.
Instance LtR128 `{LD 128} : TD 128 := {}.
Instance RtR128 `{RD 128} : TD 128 := {}.
Instance Ttb128 `{TD 128} : BD (S 128) := {}.

Instance BtL129 `{BD 129} : LD 129 := {}.
Instance BtR129 `{BD 129} : RD 129 := {}.
Instance LtR129 `{LD 129} : TD 129 := {}.
Instance RtR129 `{RD 129} : TD 129 := {}.
Instance Ttb129 `{TD 129} : BD (S 129) := {}.

Instance BtL130 `{BD 130} : LD 130 := {}.
Instance BtR130 `{BD 130} : RD 130 := {}.
Instance LtR130 `{LD 130} : TD 130 := {}.
Instance RtR130 `{RD 130} : TD 130 := {}.
Instance Ttb130 `{TD 130} : BD (S 130) := {}.

Instance BtL131 `{BD 131} : LD 131 := {}.
Instance BtR131 `{BD 131} : RD 131 := {}.
Instance LtR131 `{LD 131} : TD 131 := {}.
Instance RtR131 `{RD 131} : TD 131 := {}.
Instance Ttb131 `{TD 131} : BD (S 131) := {}.

Instance BtL132 `{BD 132} : LD 132 := {}.
Instance BtR132 `{BD 132} : RD 132 := {}.
Instance LtR132 `{LD 132} : TD 132 := {}.
Instance RtR132 `{RD 132} : TD 132 := {}.
Instance Ttb132 `{TD 132} : BD (S 132) := {}.

Instance BtL133 `{BD 133} : LD 133 := {}.
Instance BtR133 `{BD 133} : RD 133 := {}.
Instance LtR133 `{LD 133} : TD 133 := {}.
Instance RtR133 `{RD 133} : TD 133 := {}.
Instance Ttb133 `{TD 133} : BD (S 133) := {}.

Instance BtL134 `{BD 134} : LD 134 := {}.
Instance BtR134 `{BD 134} : RD 134 := {}.
Instance LtR134 `{LD 134} : TD 134 := {}.
Instance RtR134 `{RD 134} : TD 134 := {}.
Instance Ttb134 `{TD 134} : BD (S 134) := {}.

Instance BtL135 `{BD 135} : LD 135 := {}.
Instance BtR135 `{BD 135} : RD 135 := {}.
Instance LtR135 `{LD 135} : TD 135 := {}.
Instance RtR135 `{RD 135} : TD 135 := {}.
Instance Ttb135 `{TD 135} : BD (S 135) := {}.

Instance BtL136 `{BD 136} : LD 136 := {}.
Instance BtR136 `{BD 136} : RD 136 := {}.
Instance LtR136 `{LD 136} : TD 136 := {}.
Instance RtR136 `{RD 136} : TD 136 := {}.
Instance Ttb136 `{TD 136} : BD (S 136) := {}.

Instance BtL137 `{BD 137} : LD 137 := {}.
Instance BtR137 `{BD 137} : RD 137 := {}.
Instance LtR137 `{LD 137} : TD 137 := {}.
Instance RtR137 `{RD 137} : TD 137 := {}.
Instance Ttb137 `{TD 137} : BD (S 137) := {}.

Instance BtL138 `{BD 138} : LD 138 := {}.
Instance BtR138 `{BD 138} : RD 138 := {}.
Instance LtR138 `{LD 138} : TD 138 := {}.
Instance RtR138 `{RD 138} : TD 138 := {}.
Instance Ttb138 `{TD 138} : BD (S 138) := {}.

Instance BtL139 `{BD 139} : LD 139 := {}.
Instance BtR139 `{BD 139} : RD 139 := {}.
Instance LtR139 `{LD 139} : TD 139 := {}.
Instance RtR139 `{RD 139} : TD 139 := {}.
Instance Ttb139 `{TD 139} : BD (S 139) := {}.

Instance BtL140 `{BD 140} : LD 140 := {}.
Instance BtR140 `{BD 140} : RD 140 := {}.
Instance LtR140 `{LD 140} : TD 140 := {}.
Instance RtR140 `{RD 140} : TD 140 := {}.
Instance Ttb140 `{TD 140} : BD (S 140) := {}.

Instance BtL141 `{BD 141} : LD 141 := {}.
Instance BtR141 `{BD 141} : RD 141 := {}.
Instance LtR141 `{LD 141} : TD 141 := {}.
Instance RtR141 `{RD 141} : TD 141 := {}.
Instance Ttb141 `{TD 141} : BD (S 141) := {}.

Instance BtL142 `{BD 142} : LD 142 := {}.
Instance BtR142 `{BD 142} : RD 142 := {}.
Instance LtR142 `{LD 142} : TD 142 := {}.
Instance RtR142 `{RD 142} : TD 142 := {}.
Instance Ttb142 `{TD 142} : BD (S 142) := {}.

Instance BtL143 `{BD 143} : LD 143 := {}.
Instance BtR143 `{BD 143} : RD 143 := {}.
Instance LtR143 `{LD 143} : TD 143 := {}.
Instance RtR143 `{RD 143} : TD 143 := {}.
Instance Ttb143 `{TD 143} : BD (S 143) := {}.

Instance BtL144 `{BD 144} : LD 144 := {}.
Instance BtR144 `{BD 144} : RD 144 := {}.
Instance LtR144 `{LD 144} : TD 144 := {}.
Instance RtR144 `{RD 144} : TD 144 := {}.
Instance Ttb144 `{TD 144} : BD (S 144) := {}.

Instance BtL145 `{BD 145} : LD 145 := {}.
Instance BtR145 `{BD 145} : RD 145 := {}.
Instance LtR145 `{LD 145} : TD 145 := {}.
Instance RtR145 `{RD 145} : TD 145 := {}.
Instance Ttb145 `{TD 145} : BD (S 145) := {}.

Instance BtL146 `{BD 146} : LD 146 := {}.
Instance BtR146 `{BD 146} : RD 146 := {}.
Instance LtR146 `{LD 146} : TD 146 := {}.
Instance RtR146 `{RD 146} : TD 146 := {}.
Instance Ttb146 `{TD 146} : BD (S 146) := {}.

Instance BtL147 `{BD 147} : LD 147 := {}.
Instance BtR147 `{BD 147} : RD 147 := {}.
Instance LtR147 `{LD 147} : TD 147 := {}.
Instance RtR147 `{RD 147} : TD 147 := {}.
Instance Ttb147 `{TD 147} : BD (S 147) := {}.

Instance BtL148 `{BD 148} : LD 148 := {}.
Instance BtR148 `{BD 148} : RD 148 := {}.
Instance LtR148 `{LD 148} : TD 148 := {}.
Instance RtR148 `{RD 148} : TD 148 := {}.
Instance Ttb148 `{TD 148} : BD (S 148) := {}.

Instance BtL149 `{BD 149} : LD 149 := {}.
Instance BtR149 `{BD 149} : RD 149 := {}.
Instance LtR149 `{LD 149} : TD 149 := {}.
Instance RtR149 `{RD 149} : TD 149 := {}.
Instance Ttb149 `{TD 149} : BD (S 149) := {}.

Instance BtL150 `{BD 150} : LD 150 := {}.
Instance BtR150 `{BD 150} : RD 150 := {}.
Instance LtR150 `{LD 150} : TD 150 := {}.
Instance RtR150 `{RD 150} : TD 150 := {}.
Instance Ttb150 `{TD 150} : BD (S 150) := {}.

Instance BtL151 `{BD 151} : LD 151 := {}.
Instance BtR151 `{BD 151} : RD 151 := {}.
Instance LtR151 `{LD 151} : TD 151 := {}.
Instance RtR151 `{RD 151} : TD 151 := {}.
Instance Ttb151 `{TD 151} : BD (S 151) := {}.

Instance BtL152 `{BD 152} : LD 152 := {}.
Instance BtR152 `{BD 152} : RD 152 := {}.
Instance LtR152 `{LD 152} : TD 152 := {}.
Instance RtR152 `{RD 152} : TD 152 := {}.
Instance Ttb152 `{TD 152} : BD (S 152) := {}.

Instance BtL153 `{BD 153} : LD 153 := {}.
Instance BtR153 `{BD 153} : RD 153 := {}.
Instance LtR153 `{LD 153} : TD 153 := {}.
Instance RtR153 `{RD 153} : TD 153 := {}.
Instance Ttb153 `{TD 153} : BD (S 153) := {}.

Instance BtL154 `{BD 154} : LD 154 := {}.
Instance BtR154 `{BD 154} : RD 154 := {}.
Instance LtR154 `{LD 154} : TD 154 := {}.
Instance RtR154 `{RD 154} : TD 154 := {}.
Instance Ttb154 `{TD 154} : BD (S 154) := {}.

Instance BtL155 `{BD 155} : LD 155 := {}.
Instance BtR155 `{BD 155} : RD 155 := {}.
Instance LtR155 `{LD 155} : TD 155 := {}.
Instance RtR155 `{RD 155} : TD 155 := {}.
Instance Ttb155 `{TD 155} : BD (S 155) := {}.

Instance BtL156 `{BD 156} : LD 156 := {}.
Instance BtR156 `{BD 156} : RD 156 := {}.
Instance LtR156 `{LD 156} : TD 156 := {}.
Instance RtR156 `{RD 156} : TD 156 := {}.
Instance Ttb156 `{TD 156} : BD (S 156) := {}.

Instance BtL157 `{BD 157} : LD 157 := {}.
Instance BtR157 `{BD 157} : RD 157 := {}.
Instance LtR157 `{LD 157} : TD 157 := {}.
Instance RtR157 `{RD 157} : TD 157 := {}.
Instance Ttb157 `{TD 157} : BD (S 157) := {}.

Instance BtL158 `{BD 158} : LD 158 := {}.
Instance BtR158 `{BD 158} : RD 158 := {}.
Instance LtR158 `{LD 158} : TD 158 := {}.
Instance RtR158 `{RD 158} : TD 158 := {}.
Instance Ttb158 `{TD 158} : BD (S 158) := {}.

Instance BtL159 `{BD 159} : LD 159 := {}.
Instance BtR159 `{BD 159} : RD 159 := {}.
Instance LtR159 `{LD 159} : TD 159 := {}.
Instance RtR159 `{RD 159} : TD 159 := {}.
Instance Ttb159 `{TD 159} : BD (S 159) := {}.

Instance BtL160 `{BD 160} : LD 160 := {}.
Instance BtR160 `{BD 160} : RD 160 := {}.
Instance LtR160 `{LD 160} : TD 160 := {}.
Instance RtR160 `{RD 160} : TD 160 := {}.
Instance Ttb160 `{TD 160} : BD (S 160) := {}.

Instance BtL161 `{BD 161} : LD 161 := {}.
Instance BtR161 `{BD 161} : RD 161 := {}.
Instance LtR161 `{LD 161} : TD 161 := {}.
Instance RtR161 `{RD 161} : TD 161 := {}.
Instance Ttb161 `{TD 161} : BD (S 161) := {}.

Instance BtL162 `{BD 162} : LD 162 := {}.
Instance BtR162 `{BD 162} : RD 162 := {}.
Instance LtR162 `{LD 162} : TD 162 := {}.
Instance RtR162 `{RD 162} : TD 162 := {}.
Instance Ttb162 `{TD 162} : BD (S 162) := {}.

Instance BtL163 `{BD 163} : LD 163 := {}.
Instance BtR163 `{BD 163} : RD 163 := {}.
Instance LtR163 `{LD 163} : TD 163 := {}.
Instance RtR163 `{RD 163} : TD 163 := {}.
Instance Ttb163 `{TD 163} : BD (S 163) := {}.

Instance BtL164 `{BD 164} : LD 164 := {}.
Instance BtR164 `{BD 164} : RD 164 := {}.
Instance LtR164 `{LD 164} : TD 164 := {}.
Instance RtR164 `{RD 164} : TD 164 := {}.
Instance Ttb164 `{TD 164} : BD (S 164) := {}.

Instance BtL165 `{BD 165} : LD 165 := {}.
Instance BtR165 `{BD 165} : RD 165 := {}.
Instance LtR165 `{LD 165} : TD 165 := {}.
Instance RtR165 `{RD 165} : TD 165 := {}.
Instance Ttb165 `{TD 165} : BD (S 165) := {}.

Instance BtL166 `{BD 166} : LD 166 := {}.
Instance BtR166 `{BD 166} : RD 166 := {}.
Instance LtR166 `{LD 166} : TD 166 := {}.
Instance RtR166 `{RD 166} : TD 166 := {}.
Instance Ttb166 `{TD 166} : BD (S 166) := {}.

Instance BtL167 `{BD 167} : LD 167 := {}.
Instance BtR167 `{BD 167} : RD 167 := {}.
Instance LtR167 `{LD 167} : TD 167 := {}.
Instance RtR167 `{RD 167} : TD 167 := {}.
Instance Ttb167 `{TD 167} : BD (S 167) := {}.

Instance BtL168 `{BD 168} : LD 168 := {}.
Instance BtR168 `{BD 168} : RD 168 := {}.
Instance LtR168 `{LD 168} : TD 168 := {}.
Instance RtR168 `{RD 168} : TD 168 := {}.
Instance Ttb168 `{TD 168} : BD (S 168) := {}.

Instance BtL169 `{BD 169} : LD 169 := {}.
Instance BtR169 `{BD 169} : RD 169 := {}.
Instance LtR169 `{LD 169} : TD 169 := {}.
Instance RtR169 `{RD 169} : TD 169 := {}.
Instance Ttb169 `{TD 169} : BD (S 169) := {}.

Instance BtL170 `{BD 170} : LD 170 := {}.
Instance BtR170 `{BD 170} : RD 170 := {}.
Instance LtR170 `{LD 170} : TD 170 := {}.
Instance RtR170 `{RD 170} : TD 170 := {}.
Instance Ttb170 `{TD 170} : BD (S 170) := {}.

Instance BtL171 `{BD 171} : LD 171 := {}.
Instance BtR171 `{BD 171} : RD 171 := {}.
Instance LtR171 `{LD 171} : TD 171 := {}.
Instance RtR171 `{RD 171} : TD 171 := {}.
Instance Ttb171 `{TD 171} : BD (S 171) := {}.

Instance BtL172 `{BD 172} : LD 172 := {}.
Instance BtR172 `{BD 172} : RD 172 := {}.
Instance LtR172 `{LD 172} : TD 172 := {}.
Instance RtR172 `{RD 172} : TD 172 := {}.
Instance Ttb172 `{TD 172} : BD (S 172) := {}.

Instance BtL173 `{BD 173} : LD 173 := {}.
Instance BtR173 `{BD 173} : RD 173 := {}.
Instance LtR173 `{LD 173} : TD 173 := {}.
Instance RtR173 `{RD 173} : TD 173 := {}.
Instance Ttb173 `{TD 173} : BD (S 173) := {}.

Instance BtL174 `{BD 174} : LD 174 := {}.
Instance BtR174 `{BD 174} : RD 174 := {}.
Instance LtR174 `{LD 174} : TD 174 := {}.
Instance RtR174 `{RD 174} : TD 174 := {}.
Instance Ttb174 `{TD 174} : BD (S 174) := {}.

Instance BtL175 `{BD 175} : LD 175 := {}.
Instance BtR175 `{BD 175} : RD 175 := {}.
Instance LtR175 `{LD 175} : TD 175 := {}.
Instance RtR175 `{RD 175} : TD 175 := {}.
Instance Ttb175 `{TD 175} : BD (S 175) := {}.

Instance BtL176 `{BD 176} : LD 176 := {}.
Instance BtR176 `{BD 176} : RD 176 := {}.
Instance LtR176 `{LD 176} : TD 176 := {}.
Instance RtR176 `{RD 176} : TD 176 := {}.
Instance Ttb176 `{TD 176} : BD (S 176) := {}.

Instance BtL177 `{BD 177} : LD 177 := {}.
Instance BtR177 `{BD 177} : RD 177 := {}.
Instance LtR177 `{LD 177} : TD 177 := {}.
Instance RtR177 `{RD 177} : TD 177 := {}.
Instance Ttb177 `{TD 177} : BD (S 177) := {}.

Instance BtL178 `{BD 178} : LD 178 := {}.
Instance BtR178 `{BD 178} : RD 178 := {}.
Instance LtR178 `{LD 178} : TD 178 := {}.
Instance RtR178 `{RD 178} : TD 178 := {}.
Instance Ttb178 `{TD 178} : BD (S 178) := {}.

Instance BtL179 `{BD 179} : LD 179 := {}.
Instance BtR179 `{BD 179} : RD 179 := {}.
Instance LtR179 `{LD 179} : TD 179 := {}.
Instance RtR179 `{RD 179} : TD 179 := {}.
Instance Ttb179 `{TD 179} : BD (S 179) := {}.

Instance BtL180 `{BD 180} : LD 180 := {}.
Instance BtR180 `{BD 180} : RD 180 := {}.
Instance LtR180 `{LD 180} : TD 180 := {}.
Instance RtR180 `{RD 180} : TD 180 := {}.
Instance Ttb180 `{TD 180} : BD (S 180) := {}.

Instance BtL181 `{BD 181} : LD 181 := {}.
Instance BtR181 `{BD 181} : RD 181 := {}.
Instance LtR181 `{LD 181} : TD 181 := {}.
Instance RtR181 `{RD 181} : TD 181 := {}.
Instance Ttb181 `{TD 181} : BD (S 181) := {}.

Instance BtL182 `{BD 182} : LD 182 := {}.
Instance BtR182 `{BD 182} : RD 182 := {}.
Instance LtR182 `{LD 182} : TD 182 := {}.
Instance RtR182 `{RD 182} : TD 182 := {}.
Instance Ttb182 `{TD 182} : BD (S 182) := {}.

Instance BtL183 `{BD 183} : LD 183 := {}.
Instance BtR183 `{BD 183} : RD 183 := {}.
Instance LtR183 `{LD 183} : TD 183 := {}.
Instance RtR183 `{RD 183} : TD 183 := {}.
Instance Ttb183 `{TD 183} : BD (S 183) := {}.

Instance BtL184 `{BD 184} : LD 184 := {}.
Instance BtR184 `{BD 184} : RD 184 := {}.
Instance LtR184 `{LD 184} : TD 184 := {}.
Instance RtR184 `{RD 184} : TD 184 := {}.
Instance Ttb184 `{TD 184} : BD (S 184) := {}.

Instance BtL185 `{BD 185} : LD 185 := {}.
Instance BtR185 `{BD 185} : RD 185 := {}.
Instance LtR185 `{LD 185} : TD 185 := {}.
Instance RtR185 `{RD 185} : TD 185 := {}.
Instance Ttb185 `{TD 185} : BD (S 185) := {}.

Instance BtL186 `{BD 186} : LD 186 := {}.
Instance BtR186 `{BD 186} : RD 186 := {}.
Instance LtR186 `{LD 186} : TD 186 := {}.
Instance RtR186 `{RD 186} : TD 186 := {}.
Instance Ttb186 `{TD 186} : BD (S 186) := {}.

Instance BtL187 `{BD 187} : LD 187 := {}.
Instance BtR187 `{BD 187} : RD 187 := {}.
Instance LtR187 `{LD 187} : TD 187 := {}.
Instance RtR187 `{RD 187} : TD 187 := {}.
Instance Ttb187 `{TD 187} : BD (S 187) := {}.

Instance BtL188 `{BD 188} : LD 188 := {}.
Instance BtR188 `{BD 188} : RD 188 := {}.
Instance LtR188 `{LD 188} : TD 188 := {}.
Instance RtR188 `{RD 188} : TD 188 := {}.
Instance Ttb188 `{TD 188} : BD (S 188) := {}.

Instance BtL189 `{BD 189} : LD 189 := {}.
Instance BtR189 `{BD 189} : RD 189 := {}.
Instance LtR189 `{LD 189} : TD 189 := {}.
Instance RtR189 `{RD 189} : TD 189 := {}.
Instance Ttb189 `{TD 189} : BD (S 189) := {}.

Instance BtL190 `{BD 190} : LD 190 := {}.
Instance BtR190 `{BD 190} : RD 190 := {}.
Instance LtR190 `{LD 190} : TD 190 := {}.
Instance RtR190 `{RD 190} : TD 190 := {}.
Instance Ttb190 `{TD 190} : BD (S 190) := {}.

Instance BtL191 `{BD 191} : LD 191 := {}.
Instance BtR191 `{BD 191} : RD 191 := {}.
Instance LtR191 `{LD 191} : TD 191 := {}.
Instance RtR191 `{RD 191} : TD 191 := {}.
Instance Ttb191 `{TD 191} : BD (S 191) := {}.

Instance BtL192 `{BD 192} : LD 192 := {}.
Instance BtR192 `{BD 192} : RD 192 := {}.
Instance LtR192 `{LD 192} : TD 192 := {}.
Instance RtR192 `{RD 192} : TD 192 := {}.
Instance Ttb192 `{TD 192} : BD (S 192) := {}.

Instance BtL193 `{BD 193} : LD 193 := {}.
Instance BtR193 `{BD 193} : RD 193 := {}.
Instance LtR193 `{LD 193} : TD 193 := {}.
Instance RtR193 `{RD 193} : TD 193 := {}.
Instance Ttb193 `{TD 193} : BD (S 193) := {}.

Instance BtL194 `{BD 194} : LD 194 := {}.
Instance BtR194 `{BD 194} : RD 194 := {}.
Instance LtR194 `{LD 194} : TD 194 := {}.
Instance RtR194 `{RD 194} : TD 194 := {}.
Instance Ttb194 `{TD 194} : BD (S 194) := {}.

Instance BtL195 `{BD 195} : LD 195 := {}.
Instance BtR195 `{BD 195} : RD 195 := {}.
Instance LtR195 `{LD 195} : TD 195 := {}.
Instance RtR195 `{RD 195} : TD 195 := {}.
Instance Ttb195 `{TD 195} : BD (S 195) := {}.

Instance BtL196 `{BD 196} : LD 196 := {}.
Instance BtR196 `{BD 196} : RD 196 := {}.
Instance LtR196 `{LD 196} : TD 196 := {}.
Instance RtR196 `{RD 196} : TD 196 := {}.
Instance Ttb196 `{TD 196} : BD (S 196) := {}.

Instance BtL197 `{BD 197} : LD 197 := {}.
Instance BtR197 `{BD 197} : RD 197 := {}.
Instance LtR197 `{LD 197} : TD 197 := {}.
Instance RtR197 `{RD 197} : TD 197 := {}.
Instance Ttb197 `{TD 197} : BD (S 197) := {}.

Instance BtL198 `{BD 198} : LD 198 := {}.
Instance BtR198 `{BD 198} : RD 198 := {}.
Instance LtR198 `{LD 198} : TD 198 := {}.
Instance RtR198 `{RD 198} : TD 198 := {}.
Instance Ttb198 `{TD 198} : BD (S 198) := {}.

Instance BtL199 `{BD 199} : LD 199 := {}.
Instance BtR199 `{BD 199} : RD 199 := {}.
Instance LtR199 `{LD 199} : TD 199 := {}.
Instance RtR199 `{RD 199} : TD 199 := {}.
Instance Ttb199 `{TD 199} : BD (S 199) := {}.

(* Time Instance TestBD11 : BD 11 := _. *)
(* Time Instance TestBD101 : BD 101 := _. *)
Time Instance TestBD200 : BD 200 := _.
