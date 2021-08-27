
:alectryon/pygments/cmd: Elpi Command Tactic Program Accumulate Typecheck Export Db Query Trace Bound Steps
:alectryon/pygments/tacn: elpi

.. role:: elpi-api(ghref)
   :pattern: ^(% \[$name|(external )?pred $name)

.. role:: lib(elpi-api)
   :src: LPCIC coq-elpi master elpi/coq-lib.elpi

.. role:: libred(elpi-api)
   :src: LPCIC coq-elpi master elpi/elpi-reduction.elpi

.. role:: libtac(elpi-api)
   :replace: coq\.ltac\.
   :src: LPCIC coq-elpi master elpi/elpi-ltac.elpi

.. role:: builtin(elpi-api)
   :src: LPCIC coq-elpi master coq-builtin.elpi

.. role:: stdlib(elpi-api)
   :replace: std\.
   :src: LPCIC coq-elpi master elpi-builtin.elpi

.. role:: stdlibfull(elpi-api)
   :src: LPCIC coq-elpi master elpi-builtin.elpi

.. role:: elpi-type(ghref)
   :pattern: ^(kind $name|typeabbrev $name)

.. role:: type(elpi-type)
   :src: LPCIC coq-elpi master coq-builtin.elpi

.. role:: libtype(elpi-type)
   :src: LPCIC coq-elpi master elpi/coq-lib.elpi

.. role:: stdtype(elpi-type)
   :src: LPCIC coq-elpi master elpi-builtin.elpi


.. role:: elpi-constructor(ghref)
   :pattern: ^type $name

.. role:: constructor(elpi-constructor)
   :src: LPCIC coq-elpi master coq-builtin.elpi

.. role:: stdconstructor(elpi-constructor)
   :src: LPCIC coq-elpi master elpi-builtin.elpi

.. role:: elpi-macro(ghref)
   :pattern: ^macro $name

.. role:: macro(elpi-macro)
   :src: LPCIC coq-elpi master coq-builtin.elpi

.. role:: e(code)
   :language: elpi

.. role:: elpi-ns(ghref)
   :pattern: ^namespace $name

.. role:: stdlibns(elpi-ns)
   :src: LPCIC coq-elpi master elpi-builtin.elpi

.. raw:: html

   <script>
   var style = document.createElement('style'); 
   style.textContent = `
     table.docinfo {
        border-top: none;
        border-bottom: none;
        margin: auto;
     }
     #alectryon-toggle-0 {
        display: none;
     }
     label[for="alectryon-toggle-0"] {
        display: none;
     }
     .alectryon-io {
        border-left-style: dotted;
        border-left-color: lightgrey;
        padding-left: 1em;
        margin-left: 1em;
     }
     pre.alectryon-block {
        padding-left: 1em;
     }
     label.alectryon-input.alectryon-failed {
        text-decoration: red wavy underline;
     }
     .alectryon-io label.alectryon-input::after , .alectryon-banner .alectryon-bubble::before {
       content: '';
       background: url("data:image/svg+xml,%3Csvg width='14' height='14' viewBox='0 0 3.704 3.704' xmlns='http://www.w3.org/2000/svg'%3E%3Cg fill-rule='evenodd' stroke='%23000' stroke-width='.264'%3E%3Cpath d='M.794.934h2.115M.794 1.463h1.455M.794 1.992h1.852'/%3E%3C/g%3E%3Cpath d='M.132.14v2.646h.794v.661l.926-.661h1.72V.14z' fill='none' stroke='%23000' stroke-width='.265'/%3E%3C/svg%3E") top right no-repeat;
       height: 14px;
       width: 14px;
       border-style: none;
       border-radius: 0px;
     }
     code.coq , code.elpi {
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

     .elpi {
       font-family: 'Iosevka Slab Web', 'Iosevka Web', 'Iosevka Slab', 'Iosevka', 'Fira Code', monospace;
       font-feature-settings: "XV00" 1; /* Use Coq ligatures when Iosevka is available */
      }

     .highlight .-ElpiFunction , .highlight .n-ElpiFunction { color: #795E26 }
     .highlight .-ElpiVariable , .highlight .n-ElpiVariable { color: #0000ff }
     .highlight .k-ElpiKeyword { color: #AF00DB }
     .highlight .k-ElpiMode { color: #811f3f }
     .highlight .m-ElpiInteger { color: #098658 }
     .highlight .si { color: rgb(94, 93, 93) }

     .elpi .n-ElpiFunction { color: #795E26 }
     .elpi .n-ElpiVariable { color: #0000ff }
     .elpi .k-ElpiKeyword { color: #AF00DB }
     .elpi .k-ElpiMode { color: #811f3f }
     .elpi .m-ElpiInteger { color: #098658 }
     .elpi .s2 { color: #a31515 }
     .elpi .c { color: #008000 }
     .elpi .kt { color: #2b91af }
     .elpi .si { color: rgb(94, 93, 93) }

     .admonition-title:after { content: ":" }
     .admonition-title { display: inline; margin-right: 0.5em }
     .admonition-title + p { display: inline }

     .important .admonition-title { color: rgb(197, 70, 91) }
     .important { background-color: rgb(272, 237, 243) }

     .note .admonition-title { color: rgb(42, 134, 57) }
     .note { background-color: rgb(222, 247, 222); }


   `; 
   document.getElementsByTagName('head')[0].appendChild(style); 

   </script>
