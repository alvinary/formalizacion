
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

* El _paper_ no pone una ecuación para "composition distributes over arbitrary suprema", así que no estoy seguro de haber elegido una
  interpretación correcta (elegí una parecida a la que usa Struth en su módulo de quantales).

## Puntos dudosos y/o flojos

* Puse que el supremo era la menor cota superior como hipótesis/_assumption_ del un _locale_ en vez de importar e
  instanciar la clase `complete_lattice`.

* Puse la operación de supremado y el órden parcial inducido de un semianillo idempotente como argumentos de sus _locales_, que está bastante feo.

## Puntos flojos corregidos

* Ahora los semianillos y las operaciones con lenguajes salen todas de módulos estándar importados debidamente.

* Arreglé las irregularidades con la notación que usaba para 'parchar' la ambiguedad de las expresiones.

* Ahora el supremo es un supremo de verdad.

