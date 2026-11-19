# Звіт верифікації: 02_div_xy (x div y)

## 1. Вихідна програма SIPL (`examples/02_div_xy.sipl`)

```sipl
begin
    R := 0;
    while X >= Y do
    begin
        X := X - Y;
        R := R + 1
    end
end
```

- **Крона дерева розбору:** `begin R := 0 ; while X >= Y do begin X := X - Y ; R := R + 1 end end`
- **Кількість листків:** 24
- **Перевірка крони:** OK

## 2. Семантичний терм та покрокове виведення (SEM-01)

- **Unicode:** `AS^R(0̄) · WH(S^2(gre, X⇒, Y⇒), AS^X(S^2(sub, X⇒, Y⇒)) · AS^R(S^2(add, R⇒, 1̄)))`
- **LaTeX:** `AS^{R}(\overline{0}) \cdot \mathrm{WH}(S^{2}(\mathrm{gre}, X\Rightarrow, Y\Rightarrow), AS^{X}(S^{2}(\mathrm{sub}, X\Rightarrow, Y\Rightarrow)) \cdot AS^{R}(S^{2}(\mathrm{add}, R\Rightarrow, \overline{1})))`

```text
Вихідний текст: begin
    R := 0;
    while X >= Y do
    begin
        X := X - Y;
        R := R + 1
    end
end

Крок 1 [NS_Prog]: sem_P(begin R := 0; while X >= Y do begin X := X - Y; R := R + 1 end end) = sem_S(R := 0; while X >= Y do begin X := X - Y; R := R + 1 end)  (уніфікатор: [S ↦ R := 0; while X >= Y do begin X := X - Y; R := R + 1 end])
Крок 2 [NS_Stm_Seq]: sem_S(R := 0; while X >= Y do begin X := X - Y; R := R + 1 end) = sem_S(R := 0) · sem_S(while X >= Y do begin X := X - Y; R := R + 1 end)  (уніфікатор: [S1 ↦ R := 0, S2 ↦ while X >= Y do begin X := X - Y; R := R + 1 end])
Крок 3 [NS_Stm_As]: sem_S(R := 0) = AS^R(sem_A(0))  (уніфікатор: [x ↦ R, a ↦ 0])
Крок 4 [NS_A_Num]: sem_A(0) = 0̄  (уніфікатор: [n ↦ 0])
Крок 5 [NS_Stm_Wh]: sem_S(while X >= Y do begin X := X - Y; R := R + 1 end) = WH(sem_B(X >= Y), sem_S(begin X := X - Y; R := R + 1 end))  (уніфікатор: [b ↦ X >= Y, S ↦ begin X := X - Y; R := R + 1 end])
Крок 6 [NS_B_gre]: sem_B(X >= Y) = S^2(gre, sem_A(X), sem_A(Y))  (уніфікатор: [a1 ↦ X, a2 ↦ Y])
Крок 7 [NS_A_Var]: sem_A(X) = X⇒  (уніфікатор: [x ↦ X])
Крок 8 [NS_A_Var]: sem_A(Y) = Y⇒  (уніфікатор: [x ↦ Y])
Крок 9 [NS_Stm_BE]: sem_S(begin X := X - Y; R := R + 1 end) = (sem_S(X := X - Y; R := R + 1))  (уніфікатор: [S ↦ X := X - Y; R := R + 1])
Крок 10 [NS_Stm_Seq]: sem_S(X := X - Y; R := R + 1) = sem_S(X := X - Y) · sem_S(R := R + 1)  (уніфікатор: [S1 ↦ X := X - Y, S2 ↦ R := R + 1])
Крок 11 [NS_Stm_As]: sem_S(X := X - Y) = AS^X(sem_A(X - Y))  (уніфікатор: [x ↦ X, a ↦ X - Y])
Крок 12 [NS_A_Sub]: sem_A(X - Y) = S^2(sub, sem_A(X), sem_A(Y))  (уніфікатор: [a1 ↦ X, a2 ↦ Y])
Крок 13 [NS_A_Var]: sem_A(X) = X⇒  (уніфікатор: [x ↦ X])
Крок 14 [NS_A_Var]: sem_A(Y) = Y⇒  (уніфікатор: [x ↦ Y])
Крок 15 [NS_Stm_As]: sem_S(R := R + 1) = AS^R(sem_A(R + 1))  (уніфікатор: [x ↦ R, a ↦ R + 1])
Крок 16 [NS_A_Add]: sem_A(R + 1) = S^2(add, sem_A(R), sem_A(1))  (уніфікатор: [a1 ↦ R, a2 ↦ 1])
Крок 17 [NS_A_Var]: sem_A(R) = R⇒  (уніфікатор: [x ↦ R])
Крок 18 [NS_A_Num]: sem_A(1) = 1̄  (уніфікатор: [n ↦ 1])
Отриманий семантичний терм: AS^R(0̄) · WH(S^2(gre, X⇒, Y⇒), AS^X(S^2(sub, X⇒, Y⇒)) · AS^R(S^2(add, R⇒, 1̄)))
```

## 3. Покрокове обчислення терму (SEM-02, `X=17, Y=5`)

```text
Обчислення терму AS^R(0̄) · WH(S^2(gre, X⇒, Y⇒), AS^X(S^2(sub, X⇒, Y⇒)) · AS^R(S^2(add, R⇒, 1̄))) на початковому стані st = [X ↦ 17, Y ↦ 5].
(AS^R(0̄) · WH(S^2(gre, X⇒, Y⇒), AS^X(S^2(sub, X⇒, Y⇒)) · AS^R(S^2(add, R⇒, 1̄))))(st) = (WH(S^2(gre, X⇒, Y⇒), AS^X(S^2(sub, X⇒, Y⇒)) · AS^R(S^2(add, R⇒, 1̄))))((AS^R(0̄))(st))
st_0 = AS^R(0̄)(st) = st∇[R ↦ 0̄(st)] = st∇[R ↦ 0] = [X ↦ 17, Y ↦ 5, R ↦ 0]
Застосовуємо WH(S^2(gre, X⇒, Y⇒), AS^X(S^2(sub, X⇒, Y⇒)) · AS^R(S^2(add, R⇒, 1̄))) до стану st_0 = [X ↦ 17, Y ↦ 5, R ↦ 0]:
S^2(gre, X⇒, Y⇒)(st_0) = gre(X⇒(st_0), Y⇒(st_0)) = gre(17, 5) = true
Умова циклу істинна (true), виконуємо ітерацію 1 зі стану st_0:
(AS^X(S^2(sub, X⇒, Y⇒)) · AS^R(S^2(add, R⇒, 1̄)))(st_0) = (AS^R(S^2(add, R⇒, 1̄)))((AS^X(S^2(sub, X⇒, Y⇒)))(st_0))
st_0^1 = AS^X(S^2(sub, X⇒, Y⇒))(st_0) = st_0∇[X ↦ S^2(sub, X⇒, Y⇒)(st_0)] = st_0∇[X ↦ 12] = [X ↦ 12, Y ↦ 5, R ↦ 0]
st_0^2 = AS^R(S^2(add, R⇒, 1̄))(st_0^1) = st_0^1∇[R ↦ S^2(add, R⇒, 1̄)(st_0^1)] = st_0^1∇[R ↦ 1] = [X ↦ 12, Y ↦ 5, R ↦ 1]
Стан після ітерації 1: st_1 = st_0^2 = [X ↦ 12, Y ↦ 5, R ↦ 1].
S^2(gre, X⇒, Y⇒)(st_1) = gre(X⇒(st_1), Y⇒(st_1)) = gre(12, 5) = true
Умова циклу істинна (true), виконуємо ітерацію 2 зі стану st_1:
(AS^X(S^2(sub, X⇒, Y⇒)) · AS^R(S^2(add, R⇒, 1̄)))(st_1) = (AS^R(S^2(add, R⇒, 1̄)))((AS^X(S^2(sub, X⇒, Y⇒)))(st_1))
st_1^1 = AS^X(S^2(sub, X⇒, Y⇒))(st_1) = st_1∇[X ↦ S^2(sub, X⇒, Y⇒)(st_1)] = st_1∇[X ↦ 7] = [X ↦ 7, Y ↦ 5, R ↦ 1]
st_1^2 = AS^R(S^2(add, R⇒, 1̄))(st_1^1) = st_1^1∇[R ↦ S^2(add, R⇒, 1̄)(st_1^1)] = st_1^1∇[R ↦ 2] = [X ↦ 7, Y ↦ 5, R ↦ 2]
Стан після ітерації 2: st_2 = st_1^2 = [X ↦ 7, Y ↦ 5, R ↦ 2].
S^2(gre, X⇒, Y⇒)(st_2) = gre(X⇒(st_2), Y⇒(st_2)) = gre(7, 5) = true
Умова циклу істинна (true), виконуємо ітерацію 3 зі стану st_2:
(AS^X(S^2(sub, X⇒, Y⇒)) · AS^R(S^2(add, R⇒, 1̄)))(st_2) = (AS^R(S^2(add, R⇒, 1̄)))((AS^X(S^2(sub, X⇒, Y⇒)))(st_2))
st_2^1 = AS^X(S^2(sub, X⇒, Y⇒))(st_2) = st_2∇[X ↦ S^2(sub, X⇒, Y⇒)(st_2)] = st_2∇[X ↦ 2] = [X ↦ 2, Y ↦ 5, R ↦ 2]
st_2^2 = AS^R(S^2(add, R⇒, 1̄))(st_2^1) = st_2^1∇[R ↦ S^2(add, R⇒, 1̄)(st_2^1)] = st_2^1∇[R ↦ 3] = [X ↦ 2, Y ↦ 5, R ↦ 3]
Стан після ітерації 3: st_3 = st_2^2 = [X ↦ 2, Y ↦ 5, R ↦ 3].
S^2(gre, X⇒, Y⇒)(st_3) = gre(X⇒(st_3), Y⇒(st_3)) = gre(2, 5) = false
Умова циклу на стані st_3 хибна (false); NumItWH((S^2(gre, X⇒, Y⇒), AS^X(S^2(sub, X⇒, Y⇒)) · AS^R(S^2(add, R⇒, 1̄))), st_0) = 3. Результат циклу: st_3 = [X ↦ 2, Y ↦ 5, R ↦ 3].
Результат обчислення: AS^R(0̄) · WH(S^2(gre, X⇒, Y⇒), AS^X(S^2(sub, X⇒, Y⇒)) · AS^R(S^2(add, R⇒, 1̄)))(st)↓ = st_3 = [X ↦ 2, Y ↦ 5, R ↦ 3].
```

## 4. Індуктивне доведення коректності (SEM-04, `examples/specs/02_div_xy.json`)

- **Передумова:** `X >= 0 and Y > 0`
- **Постумова:** `X_0 = R * Y + X and 0 <= X and X < Y`
- **Статус:** `proved`

```text
Статус доведення: proved
Початковий символьний стан: st = [X ↦ x, Y ↦ y]
Передумова: X >= 0 and Y > 0
Стан до початку циклу: st₀ = [X ↦ x, Y ↦ y, R ↦ 0]
Умова циклу: X ≥ Y
Індукційна гіпотеза (синтезована): st_k = [Y ↦ y, R ↦ k, X ↦ x − ky]

1. База індукції (k = 0) [proved]: st_k|_{k=0} = [X ↦ x, Y ↦ y, R ↦ 0] = st₀
   При підстановці k = 0 стан st_k збігається зі станом до циклу st₀.
2. Крок індукції (k → k + 1) [proved]: fs(st_k) = [R ↦ k + 1, X ↦ x − (k + 1)y, Y ↦ y] = st_{k+1}
   Застосування семантики тіла циклу до st_k дає точний стан st_{k+1}.
3. Умова виходу та завершуваність [proved]: k* = x div y; st_{k*} = [R ↦ x div y, X ↦ x − y·(x div y), Y ↦ y]
   Найменше k ≥ 0, для якого умова хибна: k* = x div y. Заключний стан: [R ↦ x div y, X ↦ x − y·(x div y), Y ↦ y]. Нерівність 0 ≤ x − y·(x div y) випливає з інтервальних оцінок (різниця ≤ 0). Умова x − y·(x div y) < y безпосередньо випливає з умови виходу з циклу (x − y·(x div y) < y).
4. Зворотна індукція (st^{k+1} → st^k) [proved]: y_k = y_0; r_k = r_0 − k; x_k = k·y_0 + x_0; r_k·y_k + x_k = r_0·y_0 + x_0
   База k = 0 та крок переходу st^{k+1} → st^k доведені алгебраїчно для всіх співвідношень. При k = n (стан st^n = st₀: x_n = x, y_n = y, r_n = 0) з умови завершення fb(st⁰) = false отримуємо k* = x div y.
```
