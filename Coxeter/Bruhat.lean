import Coxeter.StrongExchange

namespace Coxeter

open CoxeterSystem CoxeterGroup

variable {W : Type*} [CoxeterGroup W]

inductive lt : W → W → Prop
  | step (u w : W) (h1 : cs.IsReflection (u⁻¹ * w)) (h2 : cs.length u < cs.length w) : lt u w
  | trans {u v w : W} (h1 : lt u v) (h2 : lt v w) : lt u w

instance : LT W where
  lt := lt

end Coxeter
