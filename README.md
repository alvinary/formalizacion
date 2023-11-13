
## Resumen

Queremos formalizar el álgebra de Kleene concurrente usando el asistente de pruebas Isabelle, y mostrar que los _shuffle languages_ son modelos de esa álgebra.

## Bibliografía y librerías

* En este [artículo](https://opus.bibliothek.uni-augsburg.de/opus4/frontdoor/deliver/index/docId/68908/file/CKACONCUR.pdf) se
  define el álgebra. 
  
* La teoría `Regular Sets` ya tiene la concatenación de lenguajes, y varios lemas super útiles.

* Ya hay semianillos y reticulados completos en la librería estándar.

* La teoría  `List`  ya tiene definida la operación de mezcla (es esta, [shuffles](https://isabelle.in.tum.de/library/HOL/HOL/List.html#List.shuffles|const)).

* [Acá](https://planetmath.org/shuffleoflanguages) está eso mismo definido, pero en 'matemática normal no Isabelle'.

* Ya hay librerías de quantales y álgebras de Kleene en el _proof archive_. Además, ya hay [_concurrent kleene algebra_](https://www.isa-afp.org/sessions/c2ka_distributedsystems/#CKA), que está definida en una parte de la entrada de _communicating concurrent Kleene algebras_.

## Observaciones 'ahorratiempo'

* Las mezclas de _ab_ y _cd_ son {_abcd_, _acbd_, _acdb_ _cabd_, _cdab_, _cadb_}.

* El 1 de la interpretación con _shuffle languages_ es {ε}.

* Es importante el requisito de que _leq_ sea el orden de un reticulado completo porque los lenguages regulares pueden ser infinitos.

* El artículo de Hoare es super claro con las definiciones, y están todas bien ordenaditas en dos partes: el apéndice A, y la sección que los define.
  Después la parte de los modelos es mucho más 'pesada', y no incluye definiciones relevantes para los _shuffle languages_.

* Lo único que parece que todavía no hay en el _proof archive_ es definiciones que relacionen a las álgebras de Kleene concurrentes y los _shuffle languages_.

## Puntos dudosos y/o flojos

* El _paper_ no pone una ecuación para "composition distributes over arbitrary suprema", así que no estoy seguro de haber elegido una
  interpretación correcta (elegí una parecida a la que usa Struth en su módulo de quantales). De todos modos, eso no afecta al resto de las
  definiciones, asi que se puede corregir sin cambiar nada del resto.

* La definición de reticulado completo que armé tiene varias cosas que están mal (tiene la operación de supremado como argumento
  del _locale_, y después hay que pasársela a los otros locales, que es poco prolijo).

* La notación es fea e irregular. Por ejemplo, a veces el 'menor o igual' o alguna operación se podía leer como algo de otro módulo,
  Main, o algo más local, e Isabelle pedía desambiguar, y usando el nombre de la función en vez del infijo con el símbolo se resolvía,
  y quedó todo bastante feo / pegado con cinta.

* No sabía hacer bien los _imports_ (rompía pruebas al importar y/o no encontraba los módulos), así que copié y pegué directamente
  un par de cosas.

