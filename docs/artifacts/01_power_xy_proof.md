# Звіт верифікації: 01_power_xy (x^y)

## 1. Вихідна програма SIPL (`examples/01_power_xy.sipl`)

```sipl
begin
    R := 1;
    while Y > 0 do
    begin
        R := R * X;
        Y := Y - 1
    end
end
```

- **Крона дерева розбору:** `begin R := 1 ; while Y > 0 do begin R := R * X ; Y := Y - 1 end end`
- **Кількість листків:** 24
- **Перевірка крони:** OK

## 2. Семантичний терм та покрокове виведення (SEM-01)

- **Unicode:** `AS^R(1̄) · WH(S^2(gr, Y⇒, 0̄), AS^R(S^2(mult, R⇒, X⇒)) · AS^Y(S^2(sub, Y⇒, 1̄)))`
- **LaTeX:** `AS^{R}(\overline{1}) \cdot \mathrm{WH}(S^{2}(\mathrm{gr}, Y\Rightarrow, \overline{0}), AS^{R}(S^{2}(\mathrm{mult}, R\Rightarrow, X\Rightarrow)) \cdot AS^{Y}(S^{2}(\mathrm{sub}, Y\Rightarrow, \overline{1})))`

```text
Вихідний текст: begin
    R := 1;
    while Y > 0 do
    begin
        R := R * X;
        Y := Y - 1
    end
end

Крок 1 [NS_Prog]: sem_P(begin R := 1; while Y > 0 do begin R := R * X; Y := Y - 1 end end) = sem_S(R := 1; while Y > 0 do begin R := R * X; Y := Y - 1 end)  (уніфікатор: [S ↦ R := 1; while Y > 0 do begin R := R * X; Y := Y - 1 end])
Крок 2 [NS_Stm_Seq]: sem_S(R := 1; while Y > 0 do begin R := R * X; Y := Y - 1 end) = sem_S(R := 1) · sem_S(while Y > 0 do begin R := R * X; Y := Y - 1 end)  (уніфікатор: [S1 ↦ R := 1, S2 ↦ while Y > 0 do begin R := R * X; Y := Y - 1 end])
Крок 3 [NS_Stm_As]: sem_S(R := 1) = AS^R(sem_A(1))  (уніфікатор: [x ↦ R, a ↦ 1])
Крок 4 [NS_A_Num]: sem_A(1) = 1̄  (уніфікатор: [n ↦ 1])
Крок 5 [NS_Stm_Wh]: sem_S(while Y > 0 do begin R := R * X; Y := Y - 1 end) = WH(sem_B(Y > 0), sem_S(begin R := R * X; Y := Y - 1 end))  (уніфікатор: [b ↦ Y > 0, S ↦ begin R := R * X; Y := Y - 1 end])
Крок 6 [NS_B_gr]: sem_B(Y > 0) = S^2(gr, sem_A(Y), sem_A(0))  (уніфікатор: [a1 ↦ Y, a2 ↦ 0])
Крок 7 [NS_A_Var]: sem_A(Y) = Y⇒  (уніфікатор: [x ↦ Y])
Крок 8 [NS_A_Num]: sem_A(0) = 0̄  (уніфікатор: [n ↦ 0])
Крок 9 [NS_Stm_BE]: sem_S(begin R := R * X; Y := Y - 1 end) = (sem_S(R := R * X; Y := Y - 1))  (уніфікатор: [S ↦ R := R * X; Y := Y - 1])
Крок 10 [NS_Stm_Seq]: sem_S(R := R * X; Y := Y - 1) = sem_S(R := R * X) · sem_S(Y := Y - 1)  (уніфікатор: [S1 ↦ R := R * X, S2 ↦ Y := Y - 1])
Крок 11 [NS_Stm_As]: sem_S(R := R * X) = AS^R(sem_A(R * X))  (уніфікатор: [x ↦ R, a ↦ R * X])
Крок 12 [NS_A_Mult]: sem_A(R * X) = S^2(mult, sem_A(R), sem_A(X))  (уніфікатор: [a1 ↦ R, a2 ↦ X])
Крок 13 [NS_A_Var]: sem_A(R) = R⇒  (уніфікатор: [x ↦ R])
Крок 14 [NS_A_Var]: sem_A(X) = X⇒  (уніфікатор: [x ↦ X])
Крок 15 [NS_Stm_As]: sem_S(Y := Y - 1) = AS^Y(sem_A(Y - 1))  (уніфікатор: [x ↦ Y, a ↦ Y - 1])
Крок 16 [NS_A_Sub]: sem_A(Y - 1) = S^2(sub, sem_A(Y), sem_A(1))  (уніфікатор: [a1 ↦ Y, a2 ↦ 1])
Крок 17 [NS_A_Var]: sem_A(Y) = Y⇒  (уніфікатор: [x ↦ Y])
Крок 18 [NS_A_Num]: sem_A(1) = 1̄  (уніфікатор: [n ↦ 1])
Отриманий семантичний терм: AS^R(1̄) · WH(S^2(gr, Y⇒, 0̄), AS^R(S^2(mult, R⇒, X⇒)) · AS^Y(S^2(sub, Y⇒, 1̄)))
```

## 3. Покрокове обчислення терму (SEM-02, `X=2, Y=5`)

```text
Обчислення терму AS^R(1̄) · WH(S^2(gr, Y⇒, 0̄), AS^R(S^2(mult, R⇒, X⇒)) · AS^Y(S^2(sub, Y⇒, 1̄))) на початковому стані st = [X ↦ 2, Y ↦ 5].
(AS^R(1̄) · WH(S^2(gr, Y⇒, 0̄), AS^R(S^2(mult, R⇒, X⇒)) · AS^Y(S^2(sub, Y⇒, 1̄))))(st) = (WH(S^2(gr, Y⇒, 0̄), AS^R(S^2(mult, R⇒, X⇒)) · AS^Y(S^2(sub, Y⇒, 1̄))))((AS^R(1̄))(st))
st_0 = AS^R(1̄)(st) = st∇[R ↦ 1̄(st)] = st∇[R ↦ 1] = [X ↦ 2, Y ↦ 5, R ↦ 1]
Застосовуємо WH(S^2(gr, Y⇒, 0̄), AS^R(S^2(mult, R⇒, X⇒)) · AS^Y(S^2(sub, Y⇒, 1̄))) до стану st_0 = [X ↦ 2, Y ↦ 5, R ↦ 1]:
S^2(gr, Y⇒, 0̄)(st_0) = gr(Y⇒(st_0), 0̄(st_0)) = gr(5, 0) = true
Умова циклу істинна (true), виконуємо ітерацію 1 зі стану st_0:
(AS^R(S^2(mult, R⇒, X⇒)) · AS^Y(S^2(sub, Y⇒, 1̄)))(st_0) = (AS^Y(S^2(sub, Y⇒, 1̄)))((AS^R(S^2(mult, R⇒, X⇒)))(st_0))
st_0^1 = AS^R(S^2(mult, R⇒, X⇒))(st_0) = st_0∇[R ↦ S^2(mult, R⇒, X⇒)(st_0)] = st_0∇[R ↦ 2] = [X ↦ 2, Y ↦ 5, R ↦ 2]
st_0^2 = AS^Y(S^2(sub, Y⇒, 1̄))(st_0^1) = st_0^1∇[Y ↦ S^2(sub, Y⇒, 1̄)(st_0^1)] = st_0^1∇[Y ↦ 4] = [X ↦ 2, Y ↦ 4, R ↦ 2]
Стан після ітерації 1: st_1 = st_0^2 = [X ↦ 2, Y ↦ 4, R ↦ 2].
S^2(gr, Y⇒, 0̄)(st_1) = gr(Y⇒(st_1), 0̄(st_1)) = gr(4, 0) = true
Умова циклу істинна (true), виконуємо ітерацію 2 зі стану st_1:
(AS^R(S^2(mult, R⇒, X⇒)) · AS^Y(S^2(sub, Y⇒, 1̄)))(st_1) = (AS^Y(S^2(sub, Y⇒, 1̄)))((AS^R(S^2(mult, R⇒, X⇒)))(st_1))
st_1^1 = AS^R(S^2(mult, R⇒, X⇒))(st_1) = st_1∇[R ↦ S^2(mult, R⇒, X⇒)(st_1)] = st_1∇[R ↦ 4] = [X ↦ 2, Y ↦ 4, R ↦ 4]
st_1^2 = AS^Y(S^2(sub, Y⇒, 1̄))(st_1^1) = st_1^1∇[Y ↦ S^2(sub, Y⇒, 1̄)(st_1^1)] = st_1^1∇[Y ↦ 3] = [X ↦ 2, Y ↦ 3, R ↦ 4]
Стан після ітерації 2: st_2 = st_1^2 = [X ↦ 2, Y ↦ 3, R ↦ 4].
S^2(gr, Y⇒, 0̄)(st_2) = gr(Y⇒(st_2), 0̄(st_2)) = gr(3, 0) = true
Умова циклу істинна (true), виконуємо ітерацію 3 зі стану st_2:
(AS^R(S^2(mult, R⇒, X⇒)) · AS^Y(S^2(sub, Y⇒, 1̄)))(st_2) = (AS^Y(S^2(sub, Y⇒, 1̄)))((AS^R(S^2(mult, R⇒, X⇒)))(st_2))
st_2^1 = AS^R(S^2(mult, R⇒, X⇒))(st_2) = st_2∇[R ↦ S^2(mult, R⇒, X⇒)(st_2)] = st_2∇[R ↦ 8] = [X ↦ 2, Y ↦ 3, R ↦ 8]
st_2^2 = AS^Y(S^2(sub, Y⇒, 1̄))(st_2^1) = st_2^1∇[Y ↦ S^2(sub, Y⇒, 1̄)(st_2^1)] = st_2^1∇[Y ↦ 2] = [X ↦ 2, Y ↦ 2, R ↦ 8]
Стан після ітерації 3: st_3 = st_2^2 = [X ↦ 2, Y ↦ 2, R ↦ 8].
S^2(gr, Y⇒, 0̄)(st_3) = gr(Y⇒(st_3), 0̄(st_3)) = gr(2, 0) = true
Умова циклу істинна (true), виконуємо ітерацію 4 зі стану st_3:
(AS^R(S^2(mult, R⇒, X⇒)) · AS^Y(S^2(sub, Y⇒, 1̄)))(st_3) = (AS^Y(S^2(sub, Y⇒, 1̄)))((AS^R(S^2(mult, R⇒, X⇒)))(st_3))
st_3^1 = AS^R(S^2(mult, R⇒, X⇒))(st_3) = st_3∇[R ↦ S^2(mult, R⇒, X⇒)(st_3)] = st_3∇[R ↦ 16] = [X ↦ 2, Y ↦ 2, R ↦ 16]
st_3^2 = AS^Y(S^2(sub, Y⇒, 1̄))(st_3^1) = st_3^1∇[Y ↦ S^2(sub, Y⇒, 1̄)(st_3^1)] = st_3^1∇[Y ↦ 1] = [X ↦ 2, Y ↦ 1, R ↦ 16]
Стан після ітерації 4: st_4 = st_3^2 = [X ↦ 2, Y ↦ 1, R ↦ 16].
S^2(gr, Y⇒, 0̄)(st_4) = gr(Y⇒(st_4), 0̄(st_4)) = gr(1, 0) = true
Умова циклу істинна (true), виконуємо ітерацію 5 зі стану st_4:
(AS^R(S^2(mult, R⇒, X⇒)) · AS^Y(S^2(sub, Y⇒, 1̄)))(st_4) = (AS^Y(S^2(sub, Y⇒, 1̄)))((AS^R(S^2(mult, R⇒, X⇒)))(st_4))
st_4^1 = AS^R(S^2(mult, R⇒, X⇒))(st_4) = st_4∇[R ↦ S^2(mult, R⇒, X⇒)(st_4)] = st_4∇[R ↦ 32] = [X ↦ 2, Y ↦ 1, R ↦ 32]
st_4^2 = AS^Y(S^2(sub, Y⇒, 1̄))(st_4^1) = st_4^1∇[Y ↦ S^2(sub, Y⇒, 1̄)(st_4^1)] = st_4^1∇[Y ↦ 0] = [X ↦ 2, Y ↦ 0, R ↦ 32]
Стан після ітерації 5: st_5 = st_4^2 = [X ↦ 2, Y ↦ 0, R ↦ 32].
S^2(gr, Y⇒, 0̄)(st_5) = gr(Y⇒(st_5), 0̄(st_5)) = gr(0, 0) = false
Умова циклу на стані st_5 хибна (false); NumItWH((S^2(gr, Y⇒, 0̄), AS^R(S^2(mult, R⇒, X⇒)) · AS^Y(S^2(sub, Y⇒, 1̄))), st_0) = 5. Результат циклу: st_5 = [X ↦ 2, Y ↦ 0, R ↦ 32].
Результат обчислення: AS^R(1̄) · WH(S^2(gr, Y⇒, 0̄), AS^R(S^2(mult, R⇒, X⇒)) · AS^Y(S^2(sub, Y⇒, 1̄)))(st)↓ = st_5 = [X ↦ 2, Y ↦ 0, R ↦ 32].
```

## 4. Індуктивне доведення коректності (SEM-04, `examples/specs/01_power_xy.json`)

- **Передумова:** `Y >= 0`
- **Постумова:** `R = X_0 ^ Y_0`
- **Статус:** `proved`

```text
Статус доведення: proved
Початковий символьний стан: st = [Y ↦ y, X ↦ x]
Передумова: Y >= 0
Стан до початку циклу: st₀ = [Y ↦ y, X ↦ x, R ↦ 1]
Умова циклу: Y > 0
Індукційна гіпотеза (синтезована): st_k = [X ↦ x, R ↦ x^k, Y ↦ y − k]

1. База індукції (k = 0) [proved]: st_k|_{k=0} = [Y ↦ y, X ↦ x, R ↦ 1] = st₀
   При підстановці k = 0 стан st_k збігається зі станом до циклу st₀.
2. Крок індукції (k → k + 1) [proved]: fs(st_k) = [R ↦ x^(k + 1), Y ↦ y − (k + 1), X ↦ x] = st_{k+1}
   Застосування семантики тіла циклу до st_k дає точний стан st_{k+1}.
3. Умова виходу та завершуваність [proved]: k* = y; st_{k*} = [R ↦ x^y, Y ↦ 0, X ↦ x]
   Умова y − k > 0 стає хибною при k* = y. Заключний стан: [R ↦ x^y, Y ↦ 0, X ↦ x]. Тривіально істинно.
4. Зворотна індукція (st^{k+1} → st^k) [proved]: x_k = x_0; y_k = k + y_0; r_k·x_k^y_k = r_0·x_0^y_0
   База k = 0 та крок переходу st^{k+1} → st^k доведені алгебраїчно для всіх співвідношень. При k = n (стан st^n = st₀: y_n = y, x_n = x, r_n = 1) з умови завершення fb(st⁰) = false отримуємо k* = y.
```
