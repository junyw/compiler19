# The Taipan Language

```
<program>:
	| <declgroups> <expr>
	| <expr>
<declgroups>:
	| <declgroup>
	| <declgroup> <declgroups>
<declgroup>:
	| <decl>
	| <decl> and <declgroup>
<decl>:
	| def IDENTIFIER <tyids> (<ids>) -> <typ> : <expr>                
	| def IDENTIFIER (<ids>) -> <typ> : <expr>
	| def IDENTIFIER (<ids>) : <expr>
<ids>:
	| ε
	| <bind>, <ids>
<bind>:
	| IDENTIFIER
	| IDENTIFIER : <typ>
<typ>:
	| IDENTIFIER
	| <tyid>
	| (<types> -> <typ>)
<typs>:
	| <typ>
	| <typ>, <typs>
<tyid>: 'IDENTIFIER 
<tyids>:
	| ε
	| <tyid>, <tyids>
<expr>: ...


```

# Type Inference 





