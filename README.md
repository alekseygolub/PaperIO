# Mini AI Cup #4 , 9 place
https://aicups.ru/solution/22079/

## Предупреждение

- Это было мое первое участие в подобных чемпионатах, после 3 лет участия в школьных олимпиадах. 

## Описание алгоритма

- Перебор всех состояний до определенной глубины и их оценка;

- Чтобы оценить состояние -- попробуем найти несколько путей до своей территории, чтобы противники не имели возможности перерезать наш шлейф. Оценим эти пути и выберем максимальный среди них;

- Чтобы оценить путь -- посчитаем сколько очков он нам принесет исходя из механики игры и добавим к этому оценку местоположения(Какая-то функция, которая характеризует состояние по тому, насколько нам будет выгодно продолжить игру из этой точки);

- Добавим костылей и рандомных констант в оценочные функции, чтобы все разаботало;

- Учтем ускорение, замедление и научимся уклоняться от пилы;

## Некоторые особенности

- В своем алгоритме я не учитывал микротики, хотя подозреваю, что они бы заметно усилили игру;

- Все константы были подобраны на глаз, наверное генетика справилась бы с этим лучше;

- Пробовал избавиться от проблемы закрашивания бота противниками. Частично удалось это победить тем, что я считал зону, которую захватит противник через несколько ходов. Но осталась проблема с тем, что противник отрезает бота от его территрии и убивает, полностью закрашивает мою территорию;

- Решил не обрабатывать столкновения лоб в лоб, кажется, что часто смерть противника уменьшает количество очков, которые ты можешь заработать -- лучше избегать любых смертей; 

- Из-за полного пребора требуется много вычислительных ресурсов -- ответ на каждый тик примерно равен timelimit(400+ ms). Теперь думаю, что генерировать много рандомных путей было бы более эффективно. Правильная генерация путей решила бы много проблем связанных со штрафами за длину хвоста и изгибами; 


