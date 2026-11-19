import Lake
open Lake DSL

package «mt-carrier» where
  version := v!"0.1.0"

@[default_target]
lean_lib «MtCarrier» where
  roots := #[`MtCarrier]

@[default_target]
lean_exe «mt_carrier_dump» where
  root := `MtCarrier.DumpJson

