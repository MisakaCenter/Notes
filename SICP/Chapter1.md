# SICP魔法笔记，Part 1
作者 @MisakaCenter

## 1.正则序 应用序
- 正则序求值模式是完全展开而后规约，应用序是先求值参数而后应用。
- 应用序可以避免同一表达式重复求值（Lisp采用）

考虑如下程序：
```scheme
(define (p) (p))
(define (test x y)
    (if (= x 0)
        0
        y))
 ```
 考虑`(test 0 (p))`，如果是应用序求值，0和(p)作为被传入的参数会被立即求值，然而(p)是不停机的，会陷入死循环。如果是正则序求值，(p)则不会被执行，可以得到结果为0。以此可以判断具体解释器的求值策略。

```Scheme
(define (new_if x y z) (if x y z))
```
考虑new_if，此时由于应用序求值，所以传入的y和z会先被求值再应用于if。行为会与原生的if不同。

```Scheme
(if <predicate> <consequent> <alternative>)
```
特殊形式具有自己的求值规则：原生的if求值策略为先求值<predicate>，如果得到true则求值<consequent>，否则求值<alternative>。

而new_if会把<consequent>和<alternative>先进行求值。

所以`(if (= 1 1) (display 1) (display 2))`会返回1。

而`(new_if (= 1 1) (display 1) (display 2))`会返回21（为什么不是12？与解释器求值顺序有关，只是一个convention）

`(define A (+ 5 5))` 与 `(define (A) (+ 5 5))`不同，后者定义了一个没有参数的procedure，前者定义了一个值。

## 2.递归与迭代 

计算过程的“形状”，使用代换模型可以得到。

- 线性递归计算
  - 展开：计算过程构造起一个推迟执行的操作形成的链条
  - 收缩：这些操作的实际执行
  - 解释器需要维护要执行的操作的轨迹（所占空间与n成正比）
- 线性迭代计算
  - 用固定数量的状态变量描述状态，不需要维护轨迹，没有展开、收缩的过程
  - 理论上最小所占空间为常数

尾递归：对于迭代计算过程，具体实现中解释器只维护状态变量，在常数空间中执行递归过程的实现特点。（Scheme标准要求实现尾递归）

```Scheme
(define (+ a b);递归
  (if (= a 0)
      b
      (inc (+ (dec a) b))))

(define (+ a b);迭代
  (if (= a 0)
      b
      (+ (dec a) (inc b))))
```
展开形状：
```Scheme
(+ 4 5) ;递归
(inc (+ 3 5))
(inc (inc (+ 2 5)))
(inc (inc (inc (+ 1 5))))
(inc (inc (inc (inc (+ 0 5)))))
(inc (inc (inc (inc 5))))
(inc (inc (inc 6)))
(inc (inc 7))
(inc 8)
9
```
```Scheme
(+ 4 5) ;迭代
(+ 3 6)
(+ 2 7)
(+ 1 8)
(+ 0 9)
9
```

树形递归：Fibonacci数列，每次都有2个新的分支出现，计算形状如一颗树，计算步骤数指数增长，空间需求线性增长。

## 3.高阶函数
### 过程作为参数
- 通过将过程作为高阶过程的参数，使得高阶过程能注重于概念本身。
### lambda 匿名过程
```Scheme
((lambda (<v1> <v2> ... <vn>)
    <body>)
<exp1> <exp2> ... <expn>)
```

### let 创建局部变量（lambda的语法糖）
```Scheme
(let ((<v1> <exp1>)
      (<v2> <exp2>)
       ...
      (<vn> <expn>))
  <body>) 
```
## 4.第一公民（first-class citizens）
- 可以用变量命名
- 可以作为参数传递给过程
- 可以作为值被过程返回
- 可以包含在数据结构中
  
在Scheme里，过程是也是第一公民。