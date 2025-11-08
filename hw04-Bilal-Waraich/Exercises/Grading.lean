import Exercises.Autograder
import Exercises.Problems
import Exercises.Given

#eval exercise "01a" (runParser hello.ofListCharParser "hello") (some "hello")
#eval exercise "01b" (runParser hello.ofListCharParser "goodbye") none
#eval exercise "02a" (runParser natural.ofListCharParser "1234") (some 1234)
#eval exercise "02b" (runParser natural.ofListCharParser "") none
#eval exercise "02c" (runParser natural.ofListCharParser "hello world") none
#eval exercise "02d" (runParser natural.ofListCharParser "10 with trailing text") (some 10)
#eval exercise "03" (runParser natural_pair.ofListCharParser "10 20") (some ⟨ 10, 20 ⟩)
#eval exercise "04a" (runParser arithExpr.ofListCharParser "1+3+5") (some 9)
#eval exercise "04b" (runParser arithExpr.ofListCharParser "10+3-8") (some 5)
#eval exercise "04c" (runParser arithExpr.ofListCharParser "10-5-3") (some 2)
