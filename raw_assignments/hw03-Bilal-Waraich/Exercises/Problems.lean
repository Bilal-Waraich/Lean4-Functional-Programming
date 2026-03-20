import Exercises.Given
import Mathlib.Tactic.Linarith

-- Important note for this homework: the build will fail if you do not replace all
-- uses of `sorry` with something meaningful, since we are actually running your code.
-- This means you will get 0 points even if you solved some things.  If you want to
-- submit partial results, return dummy data from functions you haven't implemented yet.


-- Exercise 1: 1 point
-- Compute the total number of views in the database.
def Database.total_views (db : Database) : Nat :=
  db.views.length

-- Exercise 2: 2 points
-- Find the title of the series with the most episodes.
-- If there are multiple such series, return any.
-- If there are no series, return `none`.
def Database.series_with_most_episodes (db : Database) : Option String :=
  if db.series.isEmpty
  then none
  else
    let most_episodes := db.series.foldl
      (
        λ acc series =>
          match acc with
          | none => some series
          | some best => if series.episodes > best.episodes then some series else acc
      ) none
    most_episodes.map (λ series => series.title)

-- Exercise 3: 2 points
-- Same as the last exercise, but for the series with the most views.
def Database.series_with_most_views (db : Database) : Option String :=
  if db.views.isEmpty || db.series.isEmpty
  then none
  else
    let most_views := db.series.foldl
      (λ acc series =>
          match acc with
          | none => some series
          | some best =>
              let seriesViews := db.views.filter (λ v => v.series_id = series.series_id) |>.length
              let bestViews   := db.views.filter (λ v => v.series_id = best.series_id)   |>.length
              if seriesViews > bestViews then some series else acc
      ) none
    most_views.map (λ series => series.title)

-- Exercise 4: 3 points
-- Find the number of views that fall in the last billing period.
-- Billing periods are numbered by natural numbers and run for ten days each,
-- so billing period 0 is days [0, 9], billing period 1 is days [10, 19], etc.
def Database.views_in_bp (db : Database) (bp : BillingPeriod) : Nat :=
  if db.views.isEmpty
  then 0
  else db.views.filter (λ v => v.day / 10 = bp) |>.length

-- Exercise 5: 2 points
-- Compute the per-user bill for the billing period.
-- Return a list of username, bill pairs, sorted by ascending user_id.
-- There is a function `Billing.get_price` that will help you here.
def insertBy (lt : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if lt x y then x :: y :: ys else y :: insertBy lt x ys

def sortBy (lt : α → α → Bool) : List α → List α
  | [] => []
  | x :: xs => insertBy lt x (sortBy lt xs)

def Database.compute_bill_for_bp (db : Database) (bp : BillingPeriod) : List (String × Nat) :=
  let sorted_user_list := db.users.toList |> sortBy (·.fst < ·.fst)
  sorted_user_list.map ( λ (uid , user) =>
    let user_views := db.views.filter (λ v => v.user_id = uid ∧ v.day / 10 == bp) |>.length
    let bill  := user.billing.get_price user_views
    (user.name, bill)
  )
