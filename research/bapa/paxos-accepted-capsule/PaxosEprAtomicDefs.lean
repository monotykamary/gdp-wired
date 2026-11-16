import CountMachine
namespace Bapa.PaxosEprAtomicSource
open Kern
def machine : SMachine := ⟨⟨⟨[4, 5, 6, 7, 8, 9],
  [],
  [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0)],
  [],
  [(1, .tup (.var 6) (.var 5), .ite (.eq (.var 15) (.const 1)) (.const 1) (.get 1 (.tup (.var 6) (.var 5)))), (3, .tup (.var 6) (.var 7), .ite (.eq (.var 16) (.const 1)) (.const 1) (.get 3 (.tup (.var 6) (.var 7)))), (4, .tup (.var 5) (.tup (.var 6) (.var 7)), .ite (.eq (.var 17) (.const 1)) (.const 1) (.get 4 (.tup (.var 5) (.tup (.var 6) (.var 7))))), (5, .tup (.var 6) (.var 7), .ite (.eq (.var 18) (.const 1)) (.const 1) (.get 5 (.tup (.var 6) (.var 7)))), (0, .var 6, .ite (.or (.and (.eq (.var 14) (.const 1)) (.le (.const 0) (.const 0))) (.and (.not (.eq (.var 14) (.const 1))) (.eq (.get 0 (.var 6)) (.const 1)))) (.const 1) (.const 0))],
  .lt (.var 3) (.var 1),
  .and (.lt (.var 4) (.const 5)) (.and (.lt (.var 5) (.var 0)) (.and (.lt (.var 9) (.var 0)) (.and (.lt (.var 6) (.var 1)) (.and (.lt (.var 8) (.var 1)) (.and (.lt (.var 7) (.var 2)) (.or (.not (.or (.eq (.var 4) (.const 2)) (.eq (.var 4) (.const 4)))) (.and (.eq (.var 19) (.const 1)) (.lt (.var 0) (.mul 2 (.get 7 (.const 0)))))))))))⟩,
  [(14, .and (.eq (.var 4) (.const 0)) (.not (.eq (.var 6) (.var 3)))), (15, .and (.eq (.var 4) (.const 1)) (.and (.not (.eq (.var 6) (.var 3))) (.and (.eq (.get 0 (.var 6)) (.const 1)) (.not (.le (.const 1) (.get 2 (.tup (.var 5) (.var 6)))))))), (16, .and (.eq (.var 4) (.const 2)) (.and (.not (.eq (.var 6) (.var 3))) (.and (.eq (.var 11) (.const 1)) (.and (.eq (.var 12) (.const 1)) (.and (.eq (.var 13) (.const 1)) (.or (.eq (.var 8) (.var 3)) (.and (.le (.const 1) (.get 6 (.var 9))) (.and (.lt (.var 8) (.var 6)) (.le (.const 1) (.get 4 (.tup (.var 9) (.tup (.var 8) (.var 7))))))))))))), (17, .and (.eq (.var 4) (.const 3)) (.and (.not (.eq (.var 6) (.var 3))) (.and (.not (.le (.const 1) (.get 2 (.tup (.var 5) (.var 6))))) (.le (.const 1) (.get 3 (.tup (.var 6) (.var 7))))))), (18, .and (.eq (.var 4) (.const 4)) (.and (.not (.eq (.var 6) (.var 3))) (.eq (.get 8 (.const 0)) (.const 0))))]⟩,
  [6, 7, 8],
  [(2, 32, .ite (.or (.le (.const 1) (.get 2 (.tup (.proj 0 (.var 32)) (.proj 1 (.var 32))))) (.and (.eq (.var 15) (.const 1)) (.and (.eq (.proj 0 (.var 32)) (.var 5)) (.lt (.proj 1 (.var 32)) (.var 6))))) (.const 1) (.const 0))],
  [(11, [26], .or (.not (.lt (.var 26) (.var 2))) (.not (.le (.const 1) (.get 3 (.tup (.var 6) (.var 26)))))), (12, [27], .or (.not (.le (.const 1) (.get 6 (.var 27)))) (.le (.const 1) (.get 1 (.tup (.var 6) (.var 27))))), (13, [28, 29, 30], .or (.not (.and (.le (.const 1) (.get 6 (.var 28))) (.and (.lt (.var 29) (.var 1)) (.and (.lt (.var 30) (.var 2)) (.and (.le (.const 1) (.get 4 (.tup (.var 28) (.tup (.var 29) (.var 30))))) (.lt (.var 29) (.var 6))))))) (.and (.not (.eq (.var 8) (.var 3))) (.le (.var 29) (.var 8)))), (19, [31], .and (.le (.get 6 (.var 31)) (.const 1)) (.or (.not (.le (.const 1) (.get 6 (.var 31)))) (.lt (.var 31) (.var 0))))],
  [(11, [20]), (12, [21]), (13, [22, 23, 24]), (19, [25])],
  [],
  []⟩
def declarations : List CDecl := [⟨7, 9, 33, 34, .var 0, .ite (.le (.const 1) (.get 6 (.var 34))) (.const 1) (.const 0), 33, 0⟩, ⟨8, 10, 35, 36, .var 0, .ite (.and (.le (.const 1) (.get 6 (.var 36))) (.not (.le (.const 1) (.get 4 (.tup (.var 36) (.tup (.var 6) (.var 7))))))) (.const 1) (.const 0), 35, 0⟩]
def admission : C := .and (.lt (.var 4) (.const 5)) (.and (.lt (.var 5) (.var 0)) (.and (.lt (.var 9) (.var 0)) (.and (.lt (.var 6) (.var 1)) (.and (.lt (.var 8) (.var 1)) (.and (.lt (.var 7) (.var 2)) (.or (.not (.or (.eq (.var 4) (.const 2)) (.eq (.var 4) (.const 4)))) (.and (.eq (.var 19) (.const 1)) (.lt (.var 0) (.mul 2 (.get 7 (.const 0)))))))))))
theorem machine_admission : machine.f.m.assume = admission := rfl
abbrev sizeId : Nat := 0
def safety : SEntry := ⟨⟨.or (.not (.and (.lt (.var 37) (.var 1)) (.and (.lt (.var 38) (.var 1)) (.and (.lt (.var 39) (.var 2)) (.and (.lt (.var 40) (.var 2)) (.and (.le (.const 1) (.get 5 (.tup (.var 37) (.var 39)))) (.le (.const 1) (.get 5 (.tup (.var 38) (.var 40)))))))))) (.eq (.var 39) (.var 40)), some 37⟩, 41, [39, 38, 40], [], [], [], [], [], ([], [], .leaf [] [] [] []), ([], [], .leaf [] [] [] [])⟩
end Bapa.PaxosEprAtomicSource
