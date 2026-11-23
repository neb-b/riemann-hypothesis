module

public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.TwoTorsionU
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.Bundle0005

@[expose] public section

universe u v

namespace Formalism.L2.Th1.A

theorem zMap : ZMap.{u, v} := z_series_map_spec
theorem jetMem : JetMem.{u} := jet_mem'
theorem wpPrimeShape : WpPrimeShape.{u} := weierstrass_p_prime_shape

theorem plusZCleared : PlusZCleared.{u} := plusZCleared_of plusZ tInZ

end Formalism.L2.Th1.A
