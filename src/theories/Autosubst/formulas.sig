term : Type
form : Type

-- Term constructors
zero : term
succ : term -> term
add : term -> term -> term
mul : term -> term -> term

-- Formula constructors
Eq : term -> term -> form
Bot : form
And : form -> form -> form
Or : form -> form -> form
Implies : form -> form -> form
ForAll : (bind term in form) -> form
Exists : (bind term in form) -> form