
import Lilac.Vec.Basic

namespace Lilac

instance {α n} [BEq α] [ReflBEq α] : ReflBEq (Vec α n) where
  rfl := sorry

instance {α n} [BEq α] [LawfulBEq α] : LawfulBEq (Vec α n) where
  eq_of_beq := sorry

end Lilac
