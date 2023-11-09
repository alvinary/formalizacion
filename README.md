
## Resumen

Queremos formalizar el álgebra de Kleene concurrente usando el asistente de pruebas Isabelle, y mostrar que los _shuffle languages_ son modelos de esa álgebra.

## Observaciones 'ahorratiempo'

* Las mezclas de _ab_ y _cd_ son {_abcd_, _acbd_, _acdb_ _cabd_, _cdab_, _cadb_}.

* El 1 de la interpretación con _shuffle languages_ es {ε}.

* Es importante el requisito de que _leq_ sea el orden de un reticulado completo porque los lenguages regulares pueden ser infinitos.

* El artículo de Hoare es super claro con las definiciones, y están todas bien ordenaditas en dos partes: el apéndice A, y la sección que los define.
  Después la parte de los modelos es mucho más farragosa y no incluye los 

## Bibliografía y librerías

* En este [artículo](https://opus.bibliothek.uni-augsburg.de/opus4/frontdoor/deliver/index/docId/68908/file/CKACONCUR.pdf) se define el álgebra.

* La teoría  `List`  ya tiene definida la operación de mezcla (es esta, [shuffles](https://isabelle.in.tum.de/library/HOL/HOL/List.html#List.shuffles|const))

* Ya hay quantales y álgebras de Kleene en el proof archive, y unas álgebras de kleene concurrentes

* Ya hay semianillos y reticulados completos en la librería estándar

