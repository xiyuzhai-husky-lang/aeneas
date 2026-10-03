module
public import Aeneas.Std.Core.Marker
@[expose] public section
namespace Aeneas.Std.core.marker

/-- PhantomData is a zero-field marker; extraction already represents it as Unit. -/
@[rust_fun "core::marker::{core::default::Default<core::marker::PhantomData<@T>>}::default"]
def phantomDataDefault (_T : Type) : Aeneas.Std.Result Unit := .ok ()

theorem phantomDataDefault_eq (T : Type) : phantomDataDefault T = .ok () := rfl

end Aeneas.Std.core.marker
