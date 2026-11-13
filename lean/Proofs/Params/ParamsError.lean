import Defs

/-! Statements for `From<MissingNamedParameterError>` and `From<ParamsConfusionError>` for
`ParamsError` (spec file: `Specs/Params.lean`). -/

set_option autoImplicit false

open Aeneas Aeneas.Std Result mysql_common Defs

namespace mysql_common

/-- `From<MissingNamedParameterError> for ParamsError`: `ParamsError::Missing`. -/
theorem params.ParamsError.Insts.CoreConvertFromMissingNamedParameterError.from_eq
    (e : params.MissingNamedParameterError) :
    params.ParamsError.Insts.CoreConvertFromMissingNamedParameterError.from e =
      ok (.Missing e) := rfl

/-- `From<ParamsConfusionError> for ParamsError`: `ParamsError::Confusion`. -/
theorem params.ParamsError.Insts.CoreConvertFromParamsConfusionError.from_eq
    (e : params.ParamsConfusionError) :
    params.ParamsError.Insts.CoreConvertFromParamsConfusionError.from e = ok (.Confusion e) := rfl

end mysql_common
