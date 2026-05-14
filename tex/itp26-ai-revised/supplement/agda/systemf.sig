kind : Type
type : Type
expr : Type

-- the constructors for kind 
star : kind

-- the constructors for type
arr : type -> type -> type
all : kind -> (type -> type) -> type

-- the constructors for expr
app  : expr -> expr -> expr
lam  : type -> (expr -> expr) -> expr
tapp : expr -> type -> expr
tlam : kind -> (type -> expr) -> expr
