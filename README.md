# FP-lab-1


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

Операции над деревом сводятся на доказательных типах баллансировки дерева. 

Из-за особенностей языка не удалось реализовать функцию filter, изза невозможности предоставить доказательство сбалансированности веток дерева на этапе удаления

Изза отсутствия как такого полиморфизма в языке интерфейс не может быть вынесен в отдельную сущность в корректном виде


## Тесты:

Тестирование сводится к успешному компилированию программы. Так как доказательны стиль не позволит скомпилировать невалидную программу, то при успехе можно быть уверенными в корректности ее работы  


## Выводы:

Agda обладает строгой системой зависимых типов и базируется на доказательном подходе к программированию, он гарантирует правильную работу программы на любых этамах без неодходимости тестирования.