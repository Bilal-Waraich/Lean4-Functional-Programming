import Std.Data.HashMap

inductive Billing where
  | per_ten_days
  | per_view

abbrev UserId := Nat
abbrev SeriesId := Nat
abbrev Day := Nat
abbrev BillingPeriod := Nat

structure User where
  name : String
  billing : Billing

structure Series where
  series_id : SeriesId
  title : String
  episodes : Nat

structure View where
  user_id : UserId
  series_id : SeriesId
  episode : Nat
  day : Day

structure Database where
  users : Std.HashMap Nat User
  series : List Series
  views : List View

def funflix_views : List View := [
  ⟨ 0, 7, 2, 0 ⟩,
  ⟨ 0, 7, 1, 0 ⟩,
  ⟨ 0, 7, 0, 0 ⟩,
  ⟨ 2, 7, 2, 0 ⟩,
  ⟨ 0, 7, 4, 0 ⟩,
  ⟨ 0, 7, 6, 0 ⟩,
  ⟨ 0, 7, 3, 0 ⟩,
  ⟨ 2, 7, 1, 0 ⟩,
  ⟨ 2, 7, 3, 0 ⟩,
  ⟨ 2, 7, 0, 0 ⟩,
  ⟨ 0, 7, 5, 0 ⟩,
  ⟨ 2, 7, 5, 1 ⟩,
  ⟨ 0, 7, 8, 1 ⟩,
  ⟨ 2, 7, 4, 1 ⟩,
  ⟨ 0, 7, 7, 1 ⟩,
  ⟨ 0, 7, 9, 1 ⟩,
  ⟨ 0, 7, 11, 2 ⟩,
  ⟨ 0, 7, 10, 2 ⟩,
  ⟨ 2, 7, 7, 2 ⟩,
  ⟨ 2, 7, 6, 2 ⟩,
  ⟨ 2, 7, 8, 3 ⟩,
  ⟨ 2, 7, 10, 4 ⟩,
  ⟨ 2, 7, 9, 4 ⟩,
  ⟨ 2, 11, 3, 4 ⟩,
  ⟨ 2, 11, 2, 4 ⟩,
  ⟨ 2, 11, 1, 4 ⟩,
  ⟨ 2, 7, 11, 4 ⟩,
  ⟨ 2, 11, 4, 4 ⟩,
  ⟨ 2, 11, 0, 4 ⟩,
  ⟨ 2, 11, 9, 5 ⟩,
  ⟨ 2, 11, 6, 5 ⟩,
  ⟨ 2, 11, 5, 5 ⟩,
  ⟨ 2, 13, 0, 5 ⟩,
  ⟨ 2, 11, 7, 5 ⟩,
  ⟨ 2, 11, 8, 5 ⟩,
  ⟨ 2, 13, 2, 6 ⟩,
  ⟨ 2, 13, 1, 6 ⟩,
  ⟨ 2, 13, 5, 7 ⟩,
  ⟨ 0, 7, 0, 7 ⟩,
  ⟨ 0, 7, 2, 7 ⟩,
  ⟨ 0, 7, 3, 7 ⟩,
  ⟨ 0, 7, 4, 7 ⟩,
  ⟨ 0, 7, 1, 7 ⟩,
  ⟨ 2, 13, 4, 7 ⟩,
  ⟨ 0, 7, 5, 7 ⟩,
  ⟨ 2, 13, 3, 7 ⟩,
  ⟨ 2, 13, 6, 7 ⟩,
  ⟨ 2, 13, 8, 8 ⟩,
  ⟨ 0, 7, 0, 8 ⟩,
  ⟨ 2, 13, 7, 8 ⟩,
  ⟨ 2, 13, 9, 9 ⟩,
  ⟨ 0, 7, 1, 9 ⟩,
  ⟨ 2, 13, 11, 10 ⟩,
  ⟨ 2, 13, 12, 10 ⟩,
  ⟨ 2, 13, 10, 10 ⟩,
  ⟨ 0, 7, 4, 10 ⟩,
  ⟨ 0, 7, 2, 10 ⟩,
  ⟨ 0, 7, 5, 10 ⟩,
  ⟨ 0, 7, 3, 10 ⟩,
  ⟨ 2, 13, 14, 11 ⟩,
  ⟨ 2, 13, 15, 11 ⟩,
  ⟨ 2, 13, 13, 11 ⟩,
  ⟨ 2, 13, 17, 12 ⟩,
  ⟨ 2, 13, 18, 12 ⟩,
  ⟨ 2, 13, 16, 12 ⟩,
  ⟨ 3, 13, 4, 13 ⟩,
  ⟨ 3, 13, 3, 13 ⟩,
  ⟨ 3, 13, 0, 13 ⟩,
  ⟨ 2, 13, 19, 13 ⟩,
  ⟨ 3, 13, 2, 13 ⟩,
  ⟨ 3, 13, 1, 13 ⟩,
  ⟨ 3, 13, 5, 14 ⟩,
  ⟨ 2, 13, 20, 14 ⟩,
  ⟨ 2, 13, 21, 14 ⟩,
  ⟨ 2, 13, 22, 15 ⟩,
  ⟨ 2, 13, 23, 15 ⟩,
  ⟨ 3, 13, 6, 15 ⟩,
  ⟨ 2, 13, 24, 15 ⟩,
  ⟨ 2, 13, 25, 16 ⟩,
  ⟨ 3, 13, 7, 16 ⟩,
  ⟨ 2, 13, 26, 17 ⟩,
  ⟨ 3, 13, 8, 17 ⟩,
  ⟨ 2, 13, 28, 17 ⟩,
  ⟨ 2, 13, 27, 17 ⟩,
  ⟨ 2, 13, 29, 17 ⟩,
  ⟨ 3, 13, 9, 17 ⟩,
  ⟨ 3, 13, 10, 18 ⟩,
  ⟨ 2, 13, 30, 18 ⟩,
  ⟨ 2, 13, 31, 18 ⟩,
  ⟨ 3, 13, 1, 19 ⟩,
  ⟨ 3, 13, 0, 19 ⟩,
  ⟨ 3, 13, 12, 19 ⟩,
  ⟨ 3, 13, 11, 19 ⟩,
  ⟨ 2, 13, 32, 19 ⟩,
  ⟨ 1, 7, 0, 20 ⟩,
  ⟨ 3, 13, 2, 20 ⟩,
  ⟨ 1, 7, 1, 21 ⟩,
  ⟨ 3, 13, 4, 21 ⟩,
  ⟨ 3, 13, 3, 21 ⟩,
  ⟨ 1, 7, 2, 22 ⟩,
  ⟨ 3, 13, 5, 22 ⟩,
  ⟨ 1, 7, 3, 23 ⟩,
  ⟨ 3, 13, 6, 23 ⟩,
  ⟨ 3, 13, 7, 24 ⟩,
  ⟨ 1, 7, 4, 24 ⟩,
  ⟨ 3, 13, 8, 24 ⟩,
  ⟨ 1, 7, 5, 25 ⟩,
  ⟨ 3, 13, 9, 25 ⟩,
  ⟨ 3, 13, 10, 26 ⟩,
  ⟨ 1, 7, 6, 26 ⟩,
  ⟨ 3, 13, 0, 27 ⟩,
  ⟨ 1, 7, 7, 27 ⟩,
  ⟨ 3, 13, 12, 27 ⟩,
  ⟨ 3, 13, 11, 27 ⟩,
  ⟨ 3, 13, 1, 28 ⟩,
  ⟨ 1, 7, 8, 28 ⟩,
  ⟨ 3, 13, 3, 29 ⟩,
  ⟨ 3, 13, 2, 29 ⟩,
  ⟨ 1, 7, 9, 29 ⟩,
  ⟨ 1, 7, 10, 30 ⟩,
  ⟨ 3, 13, 5, 30 ⟩,
  ⟨ 3, 13, 4, 30 ⟩,
  ⟨ 3, 13, 6, 31 ⟩,
  ⟨ 3, 13, 7, 31 ⟩,
  ⟨ 1, 7, 11, 31 ⟩,
  ⟨ 3, 13, 8, 32 ⟩,
  ⟨ 3, 13, 9, 33 ⟩,
  ⟨ 3, 13, 10, 34 ⟩,
  ⟨ 3, 13, 12, 35 ⟩,
  ⟨ 3, 13, 1, 35 ⟩,
  ⟨ 3, 13, 0, 35 ⟩,
  ⟨ 3, 13, 11, 35 ⟩,
  ⟨ 3, 13, 3, 36 ⟩,
  ⟨ 3, 13, 2, 36 ⟩,
  ⟨ 3, 13, 5, 37 ⟩,
  ⟨ 3, 13, 4, 37 ⟩,
  ⟨ 3, 13, 6, 38 ⟩,
  ⟨ 3, 13, 7, 39 ⟩,
  ⟨ 3, 13, 9, 40 ⟩,
  ⟨ 3, 13, 10, 40 ⟩,
  ⟨ 3, 13, 8, 40 ⟩,
  ⟨ 3, 13, 11, 40 ⟩,
  ⟨ 3, 13, 12, 41 ⟩,
]

def funflix_db : Database := {
  users := Std.HashMap.ofList [⟨ 0, alice ⟩, ⟨ 1, bob ⟩, ⟨ 2, charlie ⟩, ⟨ 3, dan ⟩]
  series := [good_omens, murderbot, black_mirror],
  views := funflix_views
}
where
  alice : User := { name := "Alice", billing := Billing.per_ten_days }
  bob : User := { name := "Bob", billing := Billing.per_view }
  charlie : User := { name := "Charlie", billing := Billing.per_view }
  dan : User := { name := "Dan", billing := Billing.per_ten_days }
  good_omens : Series := { series_id := 7, title := "Good Omens", episodes := 12 }
  murderbot : Series := { series_id := 11, title := "Murderbot Diaries", episodes := 10 }
  black_mirror : Series := { series_id := 13, title := "Black Mirror", episodes := 33 }

def empty_db : Database := { users := ∅, series := [], views := [] }

def Billing.get_price (views: Nat): Billing → Nat
  | per_ten_days => 200
  | per_view => 10 * views
