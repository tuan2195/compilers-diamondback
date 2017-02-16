open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Types

let is_osx = Conf.make_bool "osx" false "Set this flag to run on osx";;

let t name program expected = name>::test_run program name expected;;

let ta name program expected = name>::test_run_anf program name expected;;

let te name program expected_err = name>::test_err program name expected_err;;

let tvg name program expected = name>::test_run_valgrind program name expected;;

let tanf name program expected = name>::fun _ ->
  assert_equal expected (anf (tag program)) ~printer:string_of_aprogram;;

let teq name actual expected = name>::fun _ ->
  assert_equal expected actual ~printer:(fun s -> s);;

let tests =
 [
  t "forty" "let x = 40 in x" "40";
  t "fals" "let x = false in x" "false";
  t "tru" "let x = true in x" "true";
  t "true1" "if true : 5 else: 10" "5";
  t "false1" "if false : 5 else: 10" "10";
  t "print1" "print(5 - 10)" "-5\n-5";

  t "m1" "5 - 5" "0";
  t "m2" "5 + 5" "10";
  t "m3" "5 * 5" "25";
  t "m4" "5 - 0" "5";
  t "m5" "5 + 0" "5";
  t "m6" "5 * 0" "0";

  t "f1" "def f(x,y): (x+y) f(1,2)" "3";
  t "f2" "def f(x,y): (x-y) f(4,1)" "3";
  t "f3" "def f(x,y,z): (x*y+z)
          def g(x,y): (x+y)
          def h(x,y): (2*x+y)
          f(g(3,4),g(2,2),g(5,6))" "39";
  t "f4" "def f(x,y,z): (x*y+z)
          def g(x,y): (x+y)
          def h(x,y): (2*x+y)
          f(g(3,4),g(2,2),h(5,9))" "47";
  t "f5" "def f(x): (if x==1: x else: 0) f(4)" "0";
  t "f6" "def f(x): (if x==1: x else: 1) f(1)" "1";
  t "f8" "def f(x): (if x==0: 1 else: (x * f(x - 1))) f(6)" "720";
  t "f9" "def f(x): (if x==0: 0 else: (x + f(x - 1))) f(24)" "300";
  t "f1_tail" "def f(x, acc): (if x==1: acc else: f(x - 1, acc * x)) f(6, 1)" "720";
  t "f2_tail" "def f(x, acc): (if x==0: acc else: f(x - 1, acc + x)) f(99, 0)" "4950";
  t "f3_tail" "def f(x, acc): (if x==1: acc else: g(x - 1, acc * x))
               def g(x, acc): (if x==1: acc+1 else: f(x - 1, acc + x)) f(16, 1)" "20643839";
  (*t "d1" "def f(x,y,z): (x*y+z)*)
          (*def f(x,y): (x+y)*)
          (*f(g(3,4),f(2,2),h(5,9))" "47";*)

  t "m7" "let x = 5 in x" "5";
  t "m8" "let x = 5, y = 6 in x + y" "11";
  t "m9" "let x = 5 + 6 in x" "11";
  t "m10" "let x = let y = 5 + 6 in y in x - 6" "5";
  t "m11" "let x = 5 in let y = 5 + x in y" "10";
  t "m12" "let x = 5, y = 6 in let z = x + y in z" "11";
  t "m13" "let x = 5, y = 6 in let z = let a = x + y in a in z" "11";

  t "m14" "let x = 5 in 5 * x" "25";
  t "m15" "let x = 5, y = 6 in x * y" "30";
  t "m16" "let x = 5, y = 6 in let z = let a = x * y in a in z" "30";

  te "e1" "let x = 5 in x + y" "The identifier y, used at <e1, 1:17-1:18>, is not in scope";
  te "e2" "def f(x,y): (x+y) g(1,2)" "The function name y, used at <e2, 1:18-1:24>, is not in scope";
  te "e3" "let x = 5 in let x = 5 in 4" "The identifier x, defined at <e3, 1:17-1:18>, shadows one defined at <e3, 1:4-1:5>";
  te "e4" "def f(x): (x)
           def f(x): (x)
           f(f(5))"
          "The function name f, redefined at <e4, 1:0-1:13>, duplicates one at <e4, 2:11-2:24>";
  te "e5" "let x = 1073741824 in x" "The number literal 1073741824, used at <e5, 1:8-1:18>, is not supported in this language";
  te "e6" "let x = -1073741825 in x" "The number literal -1073741825, used at <e6, 1:8-1:19>, is not supported in this language";
  te "e7" "def f(x): (x)
           f(5, 6)"
          "The function called at <e7, 2:11-2:18> expected an arity of 1, but received 2 arguments";
  te "e8" "def f(x, y): (x+y)
           f(5)"
          "The function called at <e8, 2:11-2:15> expected an arity of 2, but received 1 argument";
 ]

let suite =
"suite">:::tests




let () =
  run_test_tt_main suite
;;

