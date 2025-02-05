# FP lab 2


Функциональное программирование<br>
Отчет по лабораторной работе №2


**Выполнил:** <br>
Булко Егор Олегович

**Группа:**<br>
P3306

**Преподаватель:**<br>
Пенской Александр Владимирович

## Требования:

Реализовать AVLTree с интерфейсом Bag (Multiset).
Реализованная структура данных должна быть полиморфной, для неё должны быть реализованы следующие операции:
- Добавление элементов
- Удаление элементов
- Свёртка
- Фильтрация
- Отображение

Структура должна быть иммутабельной.

Структура должна представлять собой моноид.

Помимо разработки структуры данных, необходимо также протестировать её с помощью unit и property-based тестирования.
(В моему случае по договренности с преподавателем достаточно доказательного стиля программирования присущего Agda)

## Ключевые элементы реализации:

AVL дерево было реализована, как зависимый тип, от высоты дерева. 

```agda
data Tree {v} 
          (V : Key → Set v) 
          (l u : [●]) : ℕ → 
          Set (k ⊔ v ⊔ r) where
    leaf : (l<u : l [<] u) → Tree V l u 0
    node : ∀ {h lh rh}
             (k : Key)
             (v : V k)
             (bl : 〈 lh ⊔ rh 〉≡ h )
             (lk : Tree V l [ k ] lh)
             (ku : Tree V [ k ] u rh) →
             Tree V l u (suc h)
```

- Leaf предсталяет из себя лист дерева, хранящий фактический диапазон ключей этого дерева
- Node представляет из себя узел берева, хранящий ключ и связанное с ним зависимым типом значение, левое и праве поддеревя и доказательство ис сбалансированности 

Операции над деревом строятся на доказательных типах баллансировки дерева:
```agda
data 〈_⊔_〉≡_ : ℕ → ℕ → ℕ → Set where
    ∼+ : ∀ {n} → 〈 suc n ⊔ n 〉≡ suc n
    ∼0 : ∀ {n} → 〈 n ⊔ n 〉≡ n 
    ∼- : ∀ {n} → 〈 n ⊔ suc n 〉≡ suc n
```
Он гарантирет то, что любые поддеревья сбалансированы (их высоты равны)

Ввиду того, что при выполнении оперции вставка, удаление и подобных дерево может быть пербалансировано вводятся дополнительные типы описывающие дерево, которое изменило свою высоту

Увеличение размера:

```agda
_1?+〈_〉 : ∀ {ℓ} (T : ℕ → Set ℓ) → ℕ → Set ℓ
T 1?+〈 n 〉 = ∃[ inc? ] T (if inc? then suc n else n)

pattern 0+_ tr = false , tr
pattern 1+_ tr = true , tr

```

И уменьшение соответственно:

```agda

data _〈_〉?-1 {ℓ} (T : ℕ → Set ℓ) : ℕ → Set ℓ where
    _–0 : ∀ {n} → T n → T 〈 n 〉?-1
    _–1 : ∀ {n} → T n → T 〈 suc n 〉?-1
```

---

Из-за особенностей языка не удалось реализовать функцию filter, изза невозможности описать итоговый тип с неизвестным размером, а в следстии и предоставить доказательство сбалансированности этого дерева

Изза отсутствия как такого полиморфизма в языке интерфейс не может быть вынесен в отдельную сущность в корректном виде


## Тесты:

Тестирование сводится к успешному компилированию программы. Так как доказательны стиль не позволит скомпилировать невалидную программу, то при успехе можно быть уверенными в корректности ее работы  


## Выводы:

Agda обладает строгой системой зависимых типов и базируется на доказательном подходе к программированию, он гарантирует правильную работу программы на любых этамах без неодходимости тестирования.