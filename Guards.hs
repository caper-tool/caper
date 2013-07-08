
data PermissionExpression =
                FullPerm
                | VarPerm String
                | EVarPerm String
                | PlusPerm PermissionExpression PermissionExpression


type ValueExpression = ()

data GuardType =
                ZeroGT
                | NamedGT String
                | NamedPermissionGT String
                | ParametrisedGT String
                | ProductGT GuardType GuardType
                | SumGT GuardType GuardType

data Guard =
                EmptyG
                | NamedG String
                | NamedPermissionG String PermissionExpression
                | ParametrisedG String ValueExpression
                | CoParametrisedG String [ValueExpression]
                | StarG Guard Guard


