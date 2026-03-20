import Exercises.Autograder
import Exercises.Problems
import Exercises.Given

#eval exercise "01a" funflix_db.total_views 143
#eval exercise "01b" empty_db.total_views 0
#eval exercise "02a" funflix_db.series_with_most_episodes (some "Black Mirror")
#eval exercise "02b" empty_db.series_with_most_episodes none
#eval exercise "03a" funflix_db.series_with_most_views (some "Black Mirror")
#eval exercise "03b" empty_db.series_with_most_episodes none
#eval exercise "04a" (funflix_db.views_in_bp 0) 52
#eval exercise "04b" (funflix_db.views_in_bp 1) 42
#eval exercise "04c" (funflix_db.views_in_bp 2) 25
#eval exercise "04d" (funflix_db.views_in_bp 3) 19
#eval exercise "04e" (funflix_db.views_in_bp 4) 5
#eval exerciseIn "05a" (funflix_db.compute_bill_for_bp 0) [[("Alice", 200), ("Bob", 0), ("Charlie", 320), ("Dan", 200)], [("Alice", 200), ("Bob", 200), ("Charlie", 0), ("Dan", 200)]]
#eval exerciseIn "05b" (funflix_db.compute_bill_for_bp 1) [[("Alice", 200), ("Bob", 0), ("Charlie", 230), ("Dan", 200)], [("Alice", 200), ("Bob", 40), ("Charlie", 0), ("Dan", 200)]]
#eval exerciseIn "05c" (funflix_db.compute_bill_for_bp 2) [[("Alice", 200), ("Bob", 100), ("Charlie", 0), ("Dan", 200)], [("Alice", 200), ("Bob", 0), ("Charlie", 100), ("Dan", 200)]]
#eval exerciseIn "05d" (funflix_db.compute_bill_for_bp 3) [[("Alice", 200), ("Bob", 20), ("Charlie", 0), ("Dan", 200)], [("Alice", 200), ("Bob", 0), ("Charlie", 20), ("Dan", 200)]]
#eval exerciseIn "05e" (funflix_db.compute_bill_for_bp 4) [[("Alice", 200), ("Bob", 0), ("Charlie", 0), ("Dan", 200)], [("Alice", 200), ("Bob", 0), ("Charlie", 0), ("Dan", 200)]]
