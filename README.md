Egison Quote: quasi quotes for Egison expression
===========================

[Egison](http://hagi.is.s.u-tokyo.ac.jp/~egi/egison/index.html) is a purely functional programming language featured the strong pattern match faculty.
By Egison, we can represent pattern matching for data structure without normal form(set, multiset, etc.).

We can use Egison-like expression in Haskell code by this module.
(prerequisite: [The egison package](http://hackage.haskell.org/package/egison))

How to use?
===========================

We can use Egison-quote as follows

    expr = [egison| Egison expression :: Type Signature |]

Type signature **`<Typ>`** is defined by following BNF.

    <Typ> = Bool | Int | Double | Float | Double | Char | String | [<Typ>] | (<Typ>, <Typ>, ..., <Typ>) | <Typ> -> <Typ> -> ... <Typ>

* Egison *collection* have type [a].
Thus, we can't use hetero-type collection such as `{1, 'a'}`
* Egison *tuple* have type (a, b, ..).
* Egison *lambda abstraction* have arrow type.Additionally, we have some restriction in type of arguments and return value.(mention later)

We can use Egison expression following above type signature. 

Constant expression
===========================

We can embed static-evaluated Egison expression , i.e. constant expression.
such that

    combination3_2 = [egison| (match-all {1 2 3} (Multiset Integer) [<cons $x <cons $y _>> [x y]]) :: [(Int, Int)] |]

**Note**: Static expression is evaluated in *compile time* .

Lambda abstraction
===========================

We can use Egison lambda abstraction as Haskell function.

    combination :: [Int] -> Int -> [[Int]]
    combination = [egison| (lambda [$xs $k]
                             (match-all xs (List Something)
                               [(loop $l $i (between 1 k) <join _ <cons $a_i l>> _)
                                {@(loop $l $i (between 1 k) {a_i @l} {})}])) :: [Int] -> Int -> [[Int]]|]

This function can be used as follows

    > combination [1..5] 4
    [[1,2,3,4],[1,2,3,5],[1,2,4,5],[1,3,4,5],[2,3,4,5]]

However, there sre some restriction.

 * we cannot use nested lambda.
 * we cannot pass a function as argument.(for example, (Int -> Int) -> Int is invarid type signature)

**Note**: In evaluating Egison-function, we use `unsafePerformIO` function.

Example
===========================

    -- Example1
    -- http://hagi.is.s.u-tokyo.ac.jp/~egi/egison/manual/n-queen.html
    nqueen :: Int -> [[Int]]
    nqueen = [egison| (lambda [$n]
                        (match-all (between 1 n) (Multiset Integer)
                          [<cons $a_1
                             (loop $l $i (between 2 n)
                               <cons (loop $l1 $i1 (between 1 (- i 1))
                                 (& ^,(- a_i1 (- i i1))
                                    ^,(+ a_i1 (- i i1))
                                     l1)
                               $a_i)
                               l>
                           <nil>)>
                          {@(loop $l $i (between 1 n)  {a_i @l} {})}]))
                              :: Int -> [[Int]]  |]

    > nqueen 5
    [[1,3,5,2,4],[1,4,2,5,3],[2,4,1,3,5],[2,5,3,1,4],[3,1,4,2,5],[3,5,2,4,1],[4,1,3,5,2],[4,2,5,3,1],[5,2,4,1,3],[5,3,1,4,2]]

    -- Example2
    isStreight = [egison| (lambda [$hand]
                            (match hand (Multiset Integer)
                              {[<cons $n
                                 <cons ,(+ n 1)
                                  <cons ,(+ n 2)
                                   <cons ,(+ n 3)
                                    <cons ,(+ n 4) <nil>>>>>> #t]
                               [_ #f]}))
                            :: [Int] -> Bool |]

    > isStreight [1,2,3,5,6]
    False
    > isStreight [1,2,3,5,4]
    True