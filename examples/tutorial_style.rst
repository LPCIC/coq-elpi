
:alectryon/pygments/cmd: Elpi Command Tactic Program Accumulate Typecheck Export Db
:alectryon/pygments/tacn: elpi

.. role:: elpi-api(ghref)
   :pattern: ^(% \[$name|(external )?pred $name)

.. role:: lib(elpi-api)
   :src: https://github.com/LPCIC/coq-elpi/blob/master/elpi/coq-lib.elpi

.. role:: libred(elpi-api)
   :src: https://github.com/LPCIC/coq-elpi/blob/master/elpi/elpi-reduction.elpi

.. role:: libtac(elpi-api)
   :src: https://github.com/LPCIC/coq-elpi/blob/master/elpi/elpi-ltac.elpi

.. role:: builtin(elpi-api)
   :src: https://github.com/LPCIC/coq-elpi/blob/master/coq-builtin.elpi

.. role:: stdlib(elpi-api)
   :src: https://github.com/LPCIC/coq-elpi/blob/master/elpi-builtin.elpi


.. role:: elpi-type(ghref)
   :pattern: ^(kind $name|typeabbrev $name)

.. role:: type(elpi-type)
   :src: https://github.com/LPCIC/coq-elpi/blob/master/coq-builtin.elpi

.. role:: libtype(elpi-type)
   :src: https://github.com/LPCIC/coq-elpi/blob/master/elpi/coq-lib.elpi

.. role:: stdtype(elpi-type)
   :src: https://github.com/LPCIC/coq-elpi/blob/master/elpi-builtin.elpi


.. role:: elpi-constructor(ghref)
   :pattern: ^type $name

.. role:: constructor(elpi-constructor)
   :src: https://github.com/LPCIC/coq-elpi/blob/master/coq-builtin.elpi


.. role:: elpi-macro(ghref)
   :pattern: ^macro $name

.. role:: macro(elpi-macro)
   :src: https://github.com/LPCIC/coq-elpi/blob/master/coq-builtin.elpi


.. raw:: html

   <script>
   var style = document.createElement('style'); 
   style.textContent = `
     .alectryon-io {
        border-left-style: solid;
        border-left-color: lightgrey;
        padding-left: 1em;
        margin-left: 1em;
     }
     code.coq {
        border-style: solid;
        border-color: lightgrey;
        border-width: 0.1em;
        padding: 0.2em 0.3em 0.2em 0.3em;
        border-radius: 0.5em
     }
     body {
       line-height: 2;
     }
     div.warning , div.important, div.note, div.tip {
        border-style: solid;
        border-color: lightgrey;
        border-width: 0.1em;
        border-radius: 0.5em
     }
     .ghref {
       cursor: help;
       text-decoration: underline dotted;
       font-family: 'Iosevka Slab Web', 'Iosevka Web', 'Iosevka Slab', 'Iosevka', 'Fira Code', monospace;
       font-feature-settings: "XV00" 1; /* Use Coq ligatures when Iosevka is available */
       line-height: initial;
     }
   `; 
   document.getElementsByTagName('head')[0].appendChild(style); 

   </script>
