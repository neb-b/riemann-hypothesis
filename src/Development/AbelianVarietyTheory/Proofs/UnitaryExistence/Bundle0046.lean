module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0044
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0043
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmEllipticCurveHomExistsPureTypeVector
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CurveHomLift

open UniformLift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem exists_linear_lift_of_isHolTo (F : FamilyUnif Xo σ ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) {m : ℕ} (e : (Fin m → ℂ) → (Over.mk (F.u i P) ⟶ Xo.univ.t.G))
    (he : ∀ z w, e (z + w) = e z * e w) (hol : IsHolTo Set.univ fun z => (e z).left) :
    ∃ L : (Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, F.ex i P (L z) = e z := by
  have hsm : Smooth Xo.univ.t.G.hom := Xo.univ.t.semi.smooth
  have hsm' : Smooth (pullback.snd Xo.univ.t.G.hom (F.u i P)) := inferInstance
  have hol' := ExpUniqFamily.isHolTo_ex F i P hP
  have he' := F.ex_add i P hP
  have hd := isDerivAt0_fibre _ Xo.univ.t.G (F.u i P) g (F.ex i P) _ _ _ (fun z => fibPt _ (F.ex i P z))
    (IsPullback.of_hasPullback Xo.univ.t.G.hom (F.u i P))
    (fun z => ⟨fibPt_fst _ _, fibPt_snd _ _⟩) hol' (F.ex_diff i P hP)
  obtain ⟨k, k0, hka, hk⟩ := LocalLift.exists_local_lift _ (pullback.snd Xo.univ.t.G.hom (F.u i P)) m g
    (fun z => fibPt _ (e z)) (fun z => fibPt _ (F.ex i P z)) hsm'
    (fun z => fibPt_snd _ _) (fun z => fibPt_snd _ _)
    (HolFibre.isHolTo_fibPt isOpen_univ _ _ e hol) (HolFibre.isHolTo_fibPt isOpen_univ _ _ _ hol') hd
    (by simp only [map_zero_eq_one e he, map_zero_eq_one _ he'])
  have hker : ((toAddHom (F.ex i P) he').ker : Set (Fin g → ℂ)) = P.range := Set.ext fun z => F.ex_ker i P hP z
  exact (existsUnique_linearMap_lift_of_germ (ex := toAddHom e he) (ex' := toAddHom (F.ex i P) he')
    (hker ▸ isDiscrete_iff_discreteTopology.2 hP.2.2.1) hka.differentiableAt k0
    (hk.mono fun z hz => fibPt_injective _ hz)).exists

theorem isHolTo_pt (C : Curve H) : IsHolTo Set.univ fun z : Fin 1 → ℂ => C.pt (z 0) := by
  intro U f
  obtain ⟨h1, h2⟩ := C.u.hol U f
  have hd : Differentiable ℂ (fun (z : Fin 1 → ℂ) (_ : Fin C.P.g) => C.c * z 0) := by fun_prop
  refine ⟨?_, h2.comp hd.differentiableOn fun z hz => hz.2⟩
  exact isOpen_univ.inter (h1.preimage hd.continuous)

theorem pt_one (C : Curve H) : C.pt 1 = C.pt 0 := by
  have h1 := (C.u.ker _).2 ((C.lat fun _ => C.c * 1).2 ⟨1, 0, by simp⟩)
  have h0 := (C.u.ker _).2 ((C.lat fun _ => C.c * 0).2 ⟨0, 0, by simp⟩)
  rw [Curve.pt, Curve.pt, h1, h0]

theorem exists_pure_vector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ C : Curve H, ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (φ : C.P.A.left ⟶ Xo.univ.t.G.left) (x : ℂ → (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) (ε : ℤˣ), (∀ z, (x z).left = C.pt z ≫ φ) → (∀ z w, x (z + w) = x z * x w) → (∀ z, x ((1 + ((ε : ℤ) : ℂ) * H.rt0) / 2 * z) = x z ≫ Xo.univ.t.act.act H.w0) → ∃ a ∈ lat hP (((ε : ℤ) : ℂ) * H.rt0), ∀ z : ℂ, x z = F.ex i P (z • P a) := by
  intro E _ _ _ H D l Xo σ g ty F _ _ _ _ C i P hP φ x ε hx hadd hw
  obtain ⟨L, hL⟩ := exists_linear_lift_of_isHolTo F i P hP (m := 1) (fun z => x (z 0)) (fun z w => hadd _ _) (by
    simp only [hx]
    exact HolFibre.isHolTo_comp (isHolTo_pt C) φ)
  have hv : ∀ z : ℂ, x z = F.ex i P (z • L fun _ => 1) := fun z => by
    rw [← map_smul, hL]
    simp
  have h1 : x 1 = 1 := by
    rw [← map_zero_eq_one x hadd]
    exact Over.OverMorphism.ext (by rw [hx, hx, pt_one])
  rw [hv, one_smul, F.ex_ker i P hP] at h1
  obtain ⟨a, ha⟩ := h1
  rw [← ha] at hv
  refine ⟨a, fun j hj => ?_, hv⟩
  set w : ℂ := (1 + ((ε : ℤ) : ℂ) * H.rt0) / 2 with hwdef
  have key : ∀ z : ℂ, z • (w • P a - P (H.w0 • a)) ∈ P.range := fun z => by
    have e1 := hw z
    rw [hv, hv, ← F.ex_lin i P hP] at e1
    have e2 : (fun k => ty k (H.w0 : E) * (z • P a) k) = z • P (H.w0 • a) := by
      funext k
      simp only [Pi.smul_apply, smul_eq_mul, hP.1]
      ring
    have e3 := F.ex_add i P hP (z • (w • P a - P (H.w0 • a))) (z • P (H.w0 • a))
    rw [← smul_add, sub_add_cancel, smul_smul, mul_comm z w, e1, e2] at e3
    exact (F.ex_ker i P hP _).1 (mul_eq_right.1 e3.symm)
  obtain ⟨b, hb⟩ := key 1
  rw [one_smul] at hb
  have hb0 : b = 0 := eq_zero_of_line hP (hb ▸ key)
  rw [hb0, map_zero] at hb
  have e4 := congrFun hb j
  simp only [Pi.zero_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hP.1] at e4
  have e5 : 2 * ty j (H.w0 : E) = 1 + ty j (H.rt : E) := by
    have := congrArg (fun s : 𝓞 E => ty j (s : E)) H.two_weight_eq_one_add_root
    simpa [map_ofNat] using this
  by_contra hne
  apply hj
  have e6 : w = ty j (H.w0 : E) := mul_right_cancel₀ hne (sub_eq_zero.1 e4.symm)
  rw [hwdef] at e6
  linear_combination -e5 - 2 * e6

end GlobalTheory.CurveHomLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsInverseUnitTower
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_inverse_unit_tower (ν : ℕ → ℤ) (h1 : ∀ n : ℕ, 0 < n → IsCoprime (ν n) (n : ℤ))
    (h2 : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n) :
    ∃ κ : ℕ → ℤ, (∀ n : ℕ, 0 < n → (n : ℤ) ∣ κ n * ν n - 1) ∧ (∀ n : ℕ, 0 < n → IsCoprime (κ n) (n : ℤ)) ∧
      ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ κ (n * m) - κ n := by
  have h : ∀ n : ℕ, ∃ x : ℤ, 0 < n → (n : ℤ) ∣ x * ν n - 1 := by
    intro n
    by_cases hn : 0 < n
    · obtain ⟨x, y, hxy⟩ := h1 n hn
      exact ⟨x, fun _ => ⟨-y, by linear_combination hxy⟩⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose κ hκ using h
  refine ⟨κ, hκ, fun n hn => ?_, fun n m hn hm => ?_⟩
  · obtain ⟨c, hc⟩ := hκ n hn
    exact ⟨ν n, -c, by linear_combination hc⟩
  · obtain ⟨c, hc⟩ := hκ n hn
    obtain ⟨c', hc'⟩ := hκ (n * m) (Nat.mul_pos hn hm)
    obtain ⟨d, hd⟩ := h2 n m hn hm
    push_cast at hc'
    refine ⟨κ n * m * c' - κ (n * m) * c - κ (n * m) * κ n * d, ?_⟩
    linear_combination κ n * hc' - κ (n * m) * hc - κ (n * m) * κ n * hd

theorem level_smul_mem_half {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H)
    {V : Type} [AddCommGroup V] [Module (𝓞 E) V] {s : 𝓞 E} (hs : s ∈ l.Mb) {a : V}
    (ha : a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) V)) : ∃ e, s • a = l.M • e := by
  have h : s • a ∈ Ideal.span {(l.M : 𝓞 E)} • (⊤ : Submodule (𝓞 E) V) := by
    rw [← l.prod, mul_smul]
    exact Submodule.smul_mem_smul hs ha
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h
  obtain ⟨e, -, he⟩ := h
  exact ⟨e, by rw [← he, Nat.cast_smul_eq_nsmul]⟩

theorem familyUnif_lattice_genus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)), IsPeriod (U.Di i) ty P → ∃ f : ℕ → D.La →ₗ[𝓞 E] (U.Di i).La, (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ (U.Di i).EF (f n a) (f n a') - D.EF a a') ∧ ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, f l.M a = U.t i a + l.M • e := by
  intro E _ _ _ H D l Xo σ g ty U i P hP
  obtain ⟨f, ν, h1, h2, h3, h4, h5, h6, -⟩ := familyUnif_lattice_similar E H D l Xo σ g ty U i P hP
  obtain ⟨κ, hκ1, hκ2, hκ3⟩ := exists_inverse_unit_tower ν h3 h4
  obtain ⟨s, hs1, hs2, hs3⟩ := _root_.GlobalTheory.NormTower.exists_norm_tower E H l κ hκ2 hκ3
  have hinv : ∀ n : ℕ, 0 < n → ∃ r c : 𝓞 E, r * s n = 1 + n * c := by
    intro n hn
    obtain ⟨c, hc⟩ := hs1 n hn
    obtain ⟨d, hd⟩ := hκ1 n hn
    have hd' : (κ n : 𝓞 E) * (ν n : 𝓞 E) - 1 = (n : 𝓞 E) * (d : 𝓞 E) := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hd
    exact ⟨(ν n : 𝓞 E) * H.bar (s n), (ν n : 𝓞 E) * c + d, by linear_combination (ν n : 𝓞 E) * hc + hd'⟩
  refine ⟨fun n => s n • f n, fun n m hn hm a => ?_, fun n hn => ⟨fun a => ⟨?_, ?_⟩, fun a' => ?_⟩,
    fun n hn a a' => ?_, fun a ha => ?_⟩
  · obtain ⟨e, he⟩ := h1 n m hn hm a
    obtain ⟨c, hc⟩ := hs2 n m hn hm
    have hc' : s (n * m) = s n + n * c := by linear_combination hc
    refine ⟨c • f n a + s (n * m) • e, ?_⟩
    simp only [LinearMap.smul_apply]
    rw [he, hc', ← Nat.cast_smul_eq_nsmul (𝓞 E), ← Nat.cast_smul_eq_nsmul (𝓞 E)]
    module
  · rintro ⟨e, he⟩
    obtain ⟨r, c, hrc⟩ := hinv n hn
    rw [← (h2 n hn).1 a]
    refine ⟨r • e - c • f n a, ?_⟩
    rw [LinearMap.smul_apply, ← Nat.cast_smul_eq_nsmul (𝓞 E)] at he
    have h : (r * s n) • f n a = r • (n : 𝓞 E) • e := by rw [mul_smul, he]
    rw [hrc] at h
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    linear_combination (norm := module) h
  · rintro ⟨e, rfl⟩
    exact ⟨(s n • f n) e, by rw [map_nsmul]⟩
  · obtain ⟨a, e, he⟩ := (h2 n hn).2 a'
    obtain ⟨r, c, hrc⟩ := hinv n hn
    refine ⟨r • a, e - c • f n a, ?_⟩
    rw [LinearMap.smul_apply, map_smul, smul_smul, mul_comm, hrc, he, ← Nat.cast_smul_eq_nsmul (𝓞 E),
      ← Nat.cast_smul_eq_nsmul (𝓞 E)]
    module
  · obtain ⟨c, hc⟩ := hs1 n hn
    obtain ⟨d, hd⟩ := hκ1 n hn
    obtain ⟨k, hk⟩ := h5 n hn (s n • a) (s n • a')
    have hc' : H.bar (s n) * s n = (κ n : 𝓞 E) + (n : 𝓞 E) * c := by linear_combination hc
    have e1 : D.EF (s n • a) (s n • a') = κ n * D.EF a a' + n * D.EF a (c • a') := by
      rw [D.adj, smul_smul, hc', add_smul, mul_smul, Nat.cast_smul_eq_nsmul, Int.cast_smul_eq_zsmul, map_add (f := _),
        map_nsmul, map_zsmul, smul_eq_mul, nsmul_eq_mul]
    simp only [LinearMap.smul_apply, ← map_smul]
    rw [e1] at hk
    refine ⟨k + d * D.EF a a' + ν n * D.EF a (c • a'), ?_⟩
    linear_combination hk + D.EF a a' * hd
  · obtain ⟨e, he⟩ := h6 a ha
    obtain ⟨e', he'⟩ := level_smul_mem_half l hs3 ha
    refine ⟨e + f l.M e', ?_⟩
    have h : s l.M • a = a + l.M • e' := by rw [← he', sub_smul, one_smul, add_sub_cancel]
    rw [LinearMap.smul_apply, ← map_smul, h, map_add (f := _), map_nsmul, he, smul_add, add_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMeasurePreservingFrameChangeProportionalHeStatement
section
open MeasureTheory Topology Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_measurePreserving_frameChange_proportional_hermitian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (y : Frame X.Ψ r) (y' : Frame X'.Ψ r), X.Ψ = X'.Ψ → X.p0 = X'.p0 → y ∈ OrthFr X → y' ∈ OrthFr X' → (∀ (τ : X.Ψ), ∃ t : ℝ, t ≠ 0 ∧ X'.Gm.map τ.1 = (t : ℂ) • X.Gm.map τ.1) → ∃ (e : RealGrp X ≃ᵐ RealGrp X') (α : RealGrp X → RealGrp X) (u : RealGrp X), MeasurePreserving e (haarR X) (haarR X') ∧ Measurable α ∧ (∀ t, α (α t) = u⁻¹ * t * u) ∧ ∀ t (τ : X.Ψ) (τ' : X'.Ψ), τ.1 = τ'.1 → mat y' τ' * ((e (α t) τ' : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * (mat y' τ')⁻¹ = mat y τ * ((t τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * (mat y τ)⁻¹ := by
  first | exact @GlobalTheory.PeterssonFrameChange.frame_change | exact GlobalTheory.PeterssonFrameChange.frame_change | (intros; apply GlobalTheory.PeterssonFrameChange.frame_change <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointEigenbasisBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames.EigenBaseChange

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem dualMap_comp_alg {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (dualMap ψ).comp (algebraMap S (DualNumber S)) = (algebraMap T (DualNumber T)).comp ψ := by
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_dualMap {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (TrivSqZeroExt.fstHom T T T).toRingHom.comp (dualMap ψ) =
      ψ.comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
  refine RingHom.ext fun x => ?_
  simp [dualMap]

theorem dualMap_comp_epsMul {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    (dualMap ψ).comp (epsMul a) = (epsMul (ψ a)).comp (dualMap ψ) := by
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_comm]

theorem isTanAt_baseChange {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) {x : Sp S ⟶ Xo.X}
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) :
    IsTanAt (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ v) := by
  obtain ⟨h1, h2⟩ := hv
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h1, ← Category.assoc, spMap_spMap, dualMap_comp_alg, ← spMap_spMap,
      Category.assoc]
  · rw [← Category.assoc, spMap_spMap, fst_comp_dualMap, ← spMap_spMap, Category.assoc, h2]
    simp only [Hom.one_def, Over.comp_left]
    simp

theorem isEigAt_baseChange {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (ψ : S →ₐ[c.F] T) (τ : E →+* ℂ) {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsEigAt c τ v) :
    IsEigAt c τ (spMap (dualMap ψ.toRingHom) ≫ v) := by
  intro a
  rw [Category.assoc, hv a, ← Category.assoc, spMap_spMap, dualMap_comp_epsMul, ← spMap_spMap,
    Category.assoc]
  congr 3
  exact ψ.commutes _

end GlobalTheory.Frames.EigenBaseChange


open GlobalTheory.Frames.EigenBaseChange in
theorem GlobalTheory.Frames.eigenbasis_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T) (y : FrPt Xo c S) (τ : E →+* ℂ) (w : (Sp (DualNumber T) ⟶ Xo.univ.t.G.left)), IsTanAt (spMap ψ.toRingHom ≫ y.x) w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → T, IsCombAt (spMap ψ.toRingHom ≫ y.x) (fun i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i) a w := by
  intro E _ _ _ H Dw l Xo c S _ _ T _ _ ψ y τ w hw he
  let e := (Fintype.equivFin ((σ : E →+* ℂ) × Fin (Dw.mult σ))).symm
  have hS := (eigBasis_iff_tanBasis E H Dw l Xo c S y.x y.u _ e y.tan y.eig).1 y.basis
  have hT := tanBasis_baseChange E H Dw l Xo S T ψ.toRingHom y.x _ _ hS
  have key := (eigBasis_iff_tanBasis E H Dw l Xo c T (spMap ψ.toRingHom ≫ y.x)
    (fun σ i => spMap (dualMap ψ.toRingHom) ≫ y.u σ i) _ e
    (fun σ i => EigenBaseChange.isTanAt_baseChange ψ.toRingHom (y.tan σ i))
    (fun σ i => EigenBaseChange.isEigAt_baseChange ψ σ (y.eig σ i))).2 hT
  exact key τ w hw he
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TanBasisLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.TanBasisLocal

theorem dual_ext {S : Type} [CommRing S] {Y : Scheme.{0}} {n : ℕ} {h : Fin n → S}
    (hs : Ideal.span (Set.range h) = ⊤) {w w' : Sp (DualNumber S) ⟶ Y}
    (e : ∀ i, spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ w =
      spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ w') : w = w' := by
  have key := GlobalTheory.Frames.existsUnique_glue_dual S Y n h hs
    (fun i => spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ w') (by
      intro i j α β hα hβ
      rw [← Category.assoc, ← Category.assoc, spMap_comp_ring, spMap_comp_ring, ← dualMap_comp, ← dualMap_comp,
        hα, hβ])
  exact key.unique e (fun _ => rfl)

theorem base_ext {S : Type} [CommRing S] {Y : Scheme.{0}} {n : ℕ} {h : Fin n → S}
    (hs : Ideal.span (Set.range h) = ⊤) {w w' : Sp S ⟶ Y}
    (e : ∀ i, spMap (algebraMap S (Localization.Away (h i))) ≫ w =
      spMap (algebraMap S (Localization.Away (h i))) ≫ w') : w = w' :=
  (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of S) h hs).openCover.hom_ext _ _ e

theorem fst_dual {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (TrivSqZeroExt.fstHom T T T).toRingHom.comp (dualMap ψ) =
      ψ.comp (TrivSqZeroExt.fstHom S S S).toRingHom :=
  RingHom.ext fun x => by simp [dualMap]

theorem eps_alg {S : Type} [CommRing S] (a : S) :
    (epsMul a).comp (algebraMap S (DualNumber S)) = algebraMap S (DualNumber S) :=
  RingHom.ext fun x => by
    ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem one_pull {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) :
    spMap ψ ≫ (1 : Over.mk x ⟶ Xo.univ.t.G).left = (1 : Over.mk (spMap ψ ≫ x) ⟶ Xo.univ.t.G).left := by
  have e : (Over.homMk (spMap ψ) rfl : Over.mk (spMap ψ ≫ x) ⟶ Over.mk x) ≫
      (1 : Over.mk x ⟶ Xo.univ.t.G) = 1 := by
    simp [Hom.one_def]
  rw [← e, Over.comp_left]
  rfl

theorem tan_pull {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) {x : Sp S ⟶ Xo.X}
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) :
    IsTanAt (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ v) := by
  obtain ⟨h1, h2⟩ := hv
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h1, ← Category.assoc, spMap_comp_ring, dualMap_alg, ← spMap_comp_ring,
      Category.assoc]
  · rw [← Category.assoc, spMap_comp_ring, fst_dual, ← spMap_comp_ring, Category.assoc, h2, one_pull]

theorem tan_local {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {n : ℕ} {h : Fin n → S}
    (hs : Ideal.span (Set.range h) = ⊤) {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (hv : ∀ i, IsTanAt (spMap (algebraMap S (Localization.Away (h i))) ≫ x)
      (spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ v)) : IsTanAt x v := by
  refine ⟨dual_ext hs fun i => ?_, base_ext hs fun i => ?_⟩
  · rw [← Category.assoc, (hv i).1, ← Category.assoc, ← Category.assoc, spMap_comp_ring, spMap_comp_ring,
      dualMap_alg]
  · rw [one_pull, ← (hv i).2, ← Category.assoc, ← Category.assoc, spMap_comp_ring, spMap_comp_ring, fst_dual]

theorem comb_unique {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {a : Fin m → S}
    {w w' : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsCombAt x v a w) (h' : IsCombAt x v a w') : w = w' := by
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨u', hu', rfl⟩ := h'
  have : u = u' := funext fun i => Over.OverMorphism.ext ((hu i).trans (hu' i).symm)
  rw [this]

theorem comb_exists {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} (hv : ∀ i, IsTanAt x (v i)) (a : Fin m → S) :
    ∃ w, IsCombAt x v a w := by
  refine ⟨_, fun i => Over.homMk (spMap (epsMul (a i)) ≫ v i) ?_, fun i => rfl, rfl⟩
  show (spMap (epsMul (a i)) ≫ v i) ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x
  rw [Category.assoc, (hv i).1, ← Category.assoc, spMap_comp_ring, eps_alg]

theorem comb_pull_comp {S A C : Type} [CommRing S] [CommRing A] [CommRing C] {φ : S →+* A} {χ : S →+* C}
    (α : A →+* C) (hα : α.comp φ = χ) {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    {a : Fin m → A}
    (ha : IsCombAt (spMap φ ≫ x) (fun k => spMap (dualMap φ) ≫ v k) a (spMap (dualMap φ) ≫ w)) :
    IsCombAt (spMap χ ≫ x) (fun k => spMap (dualMap χ) ≫ v k) (fun j => α (a j)) (spMap (dualMap χ) ≫ w) :=
  isCombAt_pull α (by rw [← Category.assoc, spMap_comp_ring, hα])
    (fun j => by rw [← Category.assoc, spMap_comp_ring, ← dualMap_comp, hα])
    (by rw [← Category.assoc, spMap_comp_ring, ← dualMap_comp, hα]) ha

theorem coeff_compat {S A B C : Type} [CommRing S] [CommRing A] [CommRing B] [CommRing C] {φ : S →+* A}
    {ψ : S →+* B} {χ : S →+* C} (α : A →+* C) (β : B →+* C) (hα : α.comp φ = χ) (hβ : β.comp ψ = χ)
    {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (hw : IsTanAt x w) (hb : TanBasis (spMap φ ≫ x) (fun k => spMap (dualMap φ) ≫ v k))
    {a : Fin m → A} {b : Fin m → B}
    (ha : IsCombAt (spMap φ ≫ x) (fun k => spMap (dualMap φ) ≫ v k) a (spMap (dualMap φ) ≫ w))
    (hb' : IsCombAt (spMap ψ ≫ x) (fun k => spMap (dualMap ψ) ≫ v k) b (spMap (dualMap ψ) ≫ w)) :
    (fun j => α (a j)) = fun j => β (b j) := by
  have hB : TanBasis (spMap χ ≫ x) (fun k => spMap (dualMap χ) ≫ v k) := by
    have := GlobalTheory.Frames.tanBasis_baseChange E H Dw l Xo _ _ α _ m _ hb
    have e1 : spMap α ≫ spMap φ ≫ x = spMap χ ≫ x := by rw [← Category.assoc, spMap_comp_ring, hα]
    have e2 : (fun k => spMap (dualMap α) ≫ spMap (dualMap φ) ≫ v k) = fun k => spMap (dualMap χ) ≫ v k :=
      funext fun k => by rw [← Category.assoc, spMap_comp_ring, ← dualMap_comp, hα]
    rw [e1, e2] at this
    exact this
  exact (hB.2 _ (tan_pull χ hw)).unique (comb_pull_comp α hα ha) (comb_pull_comp β hβ hb')

theorem tanBasis_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (n : ℕ) (h : Fin n → S), Ideal.span (Set.range h) = ⊤ → ∀ (m : ℕ) (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)), (∀ i, TanBasis (spMap (algebraMap S (Localization.Away (h i))) ≫ x) (fun k => spMap (dualMap (algebraMap S (Localization.Away (h i)))) ≫ v k)) → TanBasis x v := by
  intro E _ _ _ H Dw l Xo S _ x n h hs m v hb
  have hv : ∀ k, IsTanAt x (v k) := fun k => tan_local hs fun i => (hb i).1 k
  have hb' : ∀ f : Set.range h, TanBasis (spMap (algebraMap S (Localization.Away f.1)) ≫ x)
      (fun k => spMap (dualMap (algebraMap S (Localization.Away f.1))) ≫ v k) := by
    rintro ⟨_, i, rfl⟩
    exact hb i
  refine ⟨hv, fun w hw => ?_⟩
  choose d hd hdu using fun f : Set.range h =>
    (hb' f).2 _ (tan_pull (algebraMap S (Localization.Away f.1)) hw)
  have compat : ∀ (k : Fin m) (f g : Set.range h),
      IsLocalization.Away.awayToAwayRight (P := Localization.Away (f * g : S)) f.1 g (d f k) =
        IsLocalization.Away.awayToAwayLeft g.1 f (d g k) := by
    intro k f g
    let α : Localization.Away f.1 →+* Localization.Away (f * g : S) :=
      IsLocalization.Away.awayToAwayRight f.1 g
    let β : Localization.Away g.1 →+* Localization.Away (f * g : S) :=
      IsLocalization.Away.awayToAwayLeft g.1 f
    have hα : α.comp (algebraMap S _) = algebraMap S _ :=
      RingHom.ext fun s => IsLocalization.Away.awayToAwayRight_eq f.1 g.1 s
    have hβ : β.comp (algebraMap S _) = algebraMap S _ :=
      RingHom.ext fun s => IsLocalization.Away.awayToAwayLeft_eq g.1 f.1 s
    exact congrFun (coeff_compat α β hα hβ hw (hb' f) (hd f) (hd g)) k
  choose c hc hcu using fun k => Localization.existsUnique_algebraMap_eq_of_span_eq_top (Set.range h) hs
    (fun f => d f k) (compat k)
  refine ⟨c, ?_, fun a ha => funext fun k => hcu k _ fun f => ?_⟩
  · obtain ⟨w', hw'⟩ := comb_exists hv c
    have : w' = w := dual_ext hs fun i => by
      let f : Set.range h := ⟨h i, i, rfl⟩
      have h1 := isCombAt_pull (algebraMap S (Localization.Away f.1)) rfl (fun _ => rfl) rfl hw'
      have e : (fun j => algebraMap S (Localization.Away f.1) (c j)) = d f := funext fun j => hc j f
      rw [e] at h1
      exact comb_unique h1 (hd f)
    exact this ▸ hw'
  · exact congrFun (hdu f _ (isCombAt_pull (algebraMap S (Localization.Away f.1)) rfl (fun _ => rfl) rfl ha)) k

end GlobalTheory.TanBasisLocal
end

