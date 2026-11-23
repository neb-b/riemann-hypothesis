module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdelicDegreeTameRamification
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.HomExtendsOverDVRHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.TwOrbConj

variable {G : Type} [Group G]

theorem mem_rStab {H : Type} [Group H] (u : H → ℂ) (k : H) : k ∈ GlobalTheory.BCT.rStab u ↔ ∀ x, u (x * k) = u x := Iff.rfl

theorem mem_twCent (θ : G →* G) (δ x : G) : x ∈ GlobalTheory.BCT.twCent θ δ ↔ x * δ = δ * θ x := Iff.rfl

theorem relIndex_map_equiv (φ : G ≃* G) (H L : Subgroup G) :
    (H.map φ.toMonoidHom).relIndex (L.map φ.toMonoidHom) = H.relIndex L := by
  first
  | (rw [Subgroup.map_equiv_eq_comap_symm, Subgroup.relIndex_comap, Subgroup.map_map]; simp)
  | exact Subgroup.relIndex_map_map_of_injective _ _ φ.injective
  | simp [Subgroup.relIndex]

theorem avg_left {H : Type} [Group H] (u : H → ℂ) (a : H) :
    GlobalTheory.BCT.avg (fun h => u (a * h)) = GlobalTheory.BCT.avg u := by
  have hR : GlobalTheory.BCT.rStab (fun h => u (a * h)) = GlobalTheory.BCT.rStab u := by
    ext k
    rw [mem_rStab, mem_rStab]
    constructor
    · intro h x
      simpa [mul_assoc] using h (a⁻¹ * x)
    · intro h x
      simpa [mul_assoc] using h (a * x)
  unfold GlobalTheory.BCT.avg
  rw [hR]
  congr 1
  have hc : ∀ q : H ⧸ GlobalTheory.BCT.rStab u, u (a * q.out) = u (a • q).out := by
    intro q
    obtain ⟨r, hr⟩ := QuotientGroup.mk_out_eq_mul (GlobalTheory.BCT.rStab u) (a * q.out)
    have hq : (a • q) = (QuotientGroup.mk (a * q.out) : H ⧸ GlobalTheory.BCT.rStab u) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [hq, hr]
    exact ((mem_rStab u r).1 r.2 (a * q.out)).symm
  simp_rw [hc]
  exact finsum_comp_equiv (f := fun q : H ⧸ GlobalTheory.BCT.rStab u => u q.out) (MulAction.toPerm a)

theorem map_conj_self (H : Subgroup G) {h : G} (hh : h ∈ H) :
    H.map (MulAut.conj h).toMonoidHom = H := by
  ext x
  rw [Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply]
  constructor
  · intro hx
    have := H.mul_mem (H.mul_mem hh hx) (H.inv_mem hh)
    simpa [mul_assoc] using this
  · intro hx
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) hx) hh

theorem map_conj_mul (L : Subgroup G) (a b : G) :
    L.map (MulAut.conj (a * b)).toMonoidHom = (L.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem twCent_conj (θ : G →* G) (δ g : G) :
    GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g) = (GlobalTheory.BCT.twCent θ δ).map (MulAut.conj g⁻¹).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv]
  have e : (MulAut.conj g⁻¹).symm x = g * x * g⁻¹ := by simp [MulAut.conj_symm_apply]
  rw [e, mem_twCent, mem_twCent, map_mul, map_mul, map_inv]
  constructor
  · intro h
    calc g * x * g⁻¹ * δ = g * (x * (g⁻¹ * δ * θ g)) * (θ g)⁻¹ := by group
      _ = g * (g⁻¹ * δ * θ g * θ x) * (θ g)⁻¹ := by rw [h]
      _ = δ * (θ g * θ x * (θ g)⁻¹) := by group
  · intro h
    calc x * (g⁻¹ * δ * θ g) = g⁻¹ * (g * x * g⁻¹ * δ) * θ g := by group
      _ = g⁻¹ * (δ * (θ g * θ x * (θ g)⁻¹)) * θ g := by rw [h]
      _ = g⁻¹ * δ * θ g * θ x := by group

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem cptPart_map (c : G) (T : Subgroup G) :
    GlobalTheory.BCT.cptPart (T.map (MulAut.conj c).toMonoidHom) = (GlobalTheory.BCT.cptPart T).map (MulAut.conj c).toMonoidHom := by
  unfold GlobalTheory.BCT.cptPart
  rw [MonoidHom.map_closure]
  congr 1
  let h : G ≃ₜ G := (Homeomorph.mulLeft c).trans (Homeomorph.mulRight c⁻¹)
  have hh : ∀ x, h x = (MulAut.conj c).toMonoidHom x := fun x => by
    simp [h, MulAut.conj_apply]
  have hz : ∀ t, (Subgroup.zpowers ((MulAut.conj c).toMonoidHom t) : Set G) = h '' (Subgroup.zpowers t : Set G) := by
    intro t
    rw [← MonoidHom.map_zpowers, Subgroup.coe_map]
    ext y
    simp only [Set.mem_image, hh]
  have hk : ∀ t, IsCompact (closure (Subgroup.zpowers ((MulAut.conj c).toMonoidHom t) : Set G)) ↔
      IsCompact (closure (Subgroup.zpowers t : Set G)) := by
    intro t
    rw [hz, ← Homeomorph.image_closure, Homeomorph.isCompact_image]
  ext x
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hc⟩
    exact ⟨t, ⟨ht, (hk t).1 hc⟩, rfl⟩
  · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
    exact ⟨⟨t, ht, rfl⟩, (hk t).2 hc⟩

theorem relIndex_conj (c : G) (T T' L L' : Subgroup G) (hT : T' = T.map (MulAut.conj c).toMonoidHom)
    (hL : L' = L.map (MulAut.conj c).toMonoidHom) :
    (T' ⊓ L').relIndex (GlobalTheory.BCT.cptPart T') = (T ⊓ L).relIndex (GlobalTheory.BCT.cptPart T) := by
  subst hT hL
  rw [← Subgroup.map_inf_eq _ _ _ (MulAut.conj c).injective, cptPart_map, relIndex_map_equiv]

def summand (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (y : G) : ℂ :=
  (((GlobalTheory.BCT.twCent θ δ ⊓ K.map (MulAut.conj y).toMonoidHom).relIndex (GlobalTheory.BCT.cptPart (GlobalTheory.BCT.twCent θ δ)) : ℕ) : ℂ) *
    GlobalTheory.BCT.avg fun k : K => f ((y * k)⁻¹ * δ * θ (y * k))

theorem twOrb_eq (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) :
    GlobalTheory.BCT.twOrb θ K δ f = ∑ᶠ q : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G),
      summand θ K δ f (Quotient.out q) := rfl

theorem summand_rep (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (y : G) {t k : G}
    (ht : t ∈ GlobalTheory.BCT.twCent θ δ) (hk : k ∈ K) : summand θ K δ f (t * y * k) = summand θ K δ f y := by
  unfold summand
  congr 1
  · exact congrArg (fun n : ℕ => (n : ℂ)) (relIndex_conj t _ _ _ _ (map_conj_self _ ht).symm
      (by rw [map_conj_mul, map_conj_mul, map_conj_self K hk]))
  · have hd : t⁻¹ * δ * θ t = δ := by
      rw [mul_assoc, ← (mem_twCent θ δ t).1 ht, inv_mul_cancel_left]
    have hfun : (fun k' : K => f ((t * y * k * k')⁻¹ * δ * θ (t * y * k * k'))) =
        fun k' : K => (fun k'' : K => f ((y * k'')⁻¹ * δ * θ (y * k''))) (⟨k, hk⟩ * k') := by
      funext k'
      congr 1
      simp only [Subgroup.coe_mul]
      calc (t * y * k * ↑k')⁻¹ * δ * θ (t * y * k * ↑k')
          = (y * (k * ↑k'))⁻¹ * (t⁻¹ * δ * θ t) * θ (y * (k * ↑k')) := by
            simp only [map_mul, _root_.mul_inv_rev]; group
        _ = (y * (k * ↑k'))⁻¹ * δ * θ (y * (k * ↑k')) := by rw [hd]
    rw [hfun]
    exact avg_left (fun k'' : K => f ((y * k'')⁻¹ * δ * θ (y * k''))) ⟨k, hk⟩

theorem summand_twist (θ : G →* G) (K : Subgroup G) (δ g : G) (f : G → ℂ) (x : G) :
    summand θ K (g⁻¹ * δ * θ g) f x = summand θ K δ f (g * x) := by
  unfold summand
  congr 1
  · exact congrArg (fun n : ℕ => (n : ℂ)) (relIndex_conj g⁻¹ _ _ _ _ (twCent_conj θ δ g)
      (by rw [← map_conj_mul, inv_mul_cancel_left]))
  · congr 1
    funext k
    congr 1
    simp only [map_mul, _root_.mul_inv_rev]
    group

def dcEquiv (θ : G →* G) (K : Subgroup G) (δ g : G) :
    DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g) : Set G) (K : Set G) ≃
      DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G) where
  toFun q := DoubleCoset.mk (GlobalTheory.BCT.twCent θ δ) K (g * Quotient.out q)
  invFun q := DoubleCoset.mk (GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g)) K (g⁻¹ * Quotient.out q)
  left_inv q := by
    obtain ⟨t, ht, k, hk, he⟩ :=
      DoubleCoset.mk_out_eq_mul (GlobalTheory.BCT.twCent θ δ) K (g * Quotient.out q)
    show DoubleCoset.mk _ K (g⁻¹ * Quotient.out (DoubleCoset.mk (GlobalTheory.BCT.twCent θ δ) K (g * Quotient.out q))) = q
    rw [he]
    conv_rhs => rw [← DoubleCoset.out_eq' (H := GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g)) (K := K) q]
    rw [DoubleCoset.eq]
    refine ⟨g⁻¹ * t⁻¹ * g, ?_, k⁻¹, K.inv_mem hk, by group⟩
    rw [twCent_conj]
    exact ⟨t⁻¹, (GlobalTheory.BCT.twCent θ δ).inv_mem ht, by simp [MulAut.conj_apply]⟩
  right_inv q := by
    obtain ⟨t, ht, k, hk, he⟩ :=
      DoubleCoset.mk_out_eq_mul (GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g)) K (g⁻¹ * Quotient.out q)
    show DoubleCoset.mk _ K (g * Quotient.out (DoubleCoset.mk (GlobalTheory.BCT.twCent θ (g⁻¹ * δ * θ g)) K
      (g⁻¹ * Quotient.out q))) = q
    rw [he]
    conv_rhs => rw [← DoubleCoset.out_eq' (H := GlobalTheory.BCT.twCent θ δ) (K := K) q]
    rw [DoubleCoset.eq]
    rw [twCent_conj] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    refine ⟨s⁻¹, (GlobalTheory.BCT.twCent θ δ).inv_mem hs, k⁻¹, K.inv_mem hk, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

end GlobalTheory.TwOrbConj

namespace GlobalTheory.TwOrbConj

theorem twOrb_twConj : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K : Subgroup G)
    (δ g : G) (f : G → ℂ), (∀ x : G, (GlobalTheory.BCT.rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0) →
    GlobalTheory.BCT.twOrb θ K (g⁻¹ * δ * θ g) f = GlobalTheory.BCT.twOrb θ K δ f := by
  intro G _ _ _ θ K δ g f _
  rw [twOrb_eq, twOrb_eq]
  calc ∑ᶠ q, summand θ K (g⁻¹ * δ * θ g) f (Quotient.out q)
      = ∑ᶠ q, summand θ K δ f (Quotient.out (dcEquiv θ K δ g q)) := by
        refine finsum_congr fun q => ?_
        rw [summand_twist]
        obtain ⟨t, ht, k, hk, he⟩ :=
          DoubleCoset.mk_out_eq_mul (GlobalTheory.BCT.twCent θ δ) K (g * Quotient.out q)
        show _ = summand θ K δ f (Quotient.out (DoubleCoset.mk (GlobalTheory.BCT.twCent θ δ) K (g * Quotient.out q)))
        rw [he, summand_rep θ K δ f _ ht hk]
    _ = ∑ᶠ q, summand θ K δ f (Quotient.out q) :=
        finsum_comp_equiv (f := fun q : DoubleCoset.Quotient (GlobalTheory.BCT.twCent θ δ : Set G) (K : Set G) =>
          summand θ K δ f (Quotient.out q)) (dcEquiv θ K δ g)

end GlobalTheory.TwOrbConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VPEqSumHeisCore
section
noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.DatumFourierCore

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.DatumFourier
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1600000 in
theorem thetaVector_eq_sum_heisenberg_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι → ∃ δ : ℤˣ, ∀ (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) → R.vP i t = ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ • ∑ᶠ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q • heisO R.ψ (Vc D i) (Wc D i) (Matrix.of fun a b => e * incA D (((δ : ℤ) : D.host.E) * ι (cSep l₂ • levRep (q b)) a / (l₂.M : D.host.E))) (R.vacP i) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i hV H Dw ι hι hI
  obtain ⟨ε, hε⟩ := hI
  refine ⟨ε, fun t l φ hφ hP e he => ?_⟩
  obtain ⟨hvac, e₁, he₁, hθ⟩ := hR.thP.vP i t
  obtain ⟨e₂, he₂, hφ⟩ := hφ
  obtain rfl := idemSum_unique (Vc D i) he₁ he
  obtain rfl := idemSum_unique (Vc D i) he₂ he
  have hβV := hR.lev.βV i
  have hβW := hR.lev.βW i
  have hS := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβV
  have hT := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβW
  have hstd : R.ΛV i = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβV, ← GlobalTheory.SplitReps.hLat_one, hV.2]
  have hlat := mem_latRat_iff hV.1 hstd hβW
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hM' : (l.M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hsurj : ∀ M ∈ GlobalTheory.LatVac.latRat (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)), ∃ x : Fin (Vc D i).rank → Dw.La, M = Matrix.of fun a b => ι (x b) a := by
    intro M hM
    choose x hx using fun b => hι.2.ge ((hlat M).1 hM b)
    exact ⟨x, Matrix.ext fun a b => (congrFun (hx b) a).symm⟩
  have hint : ∀ u ∈ latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) (fun _ => True),
      IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (cA D e • u)) := fun u hu =>
    int_of_mem_latO (fun M hM => by
      obtain ⟨x, rfl⟩ := hsurj M hM
      exact (hφ x).1) hu
  have : Finite (LevQ Dw l) := GlobalTheory.LevelPairing.finite_LevQ
  have := Fintype.ofFinite (Fin (Vc D i).rank → LevQ Dw l)
  rw [finsum_eq_sum_of_fintype, Finset.smul_sum]
  simp only [smul_smul]
  refine thetaAt_eq_sum _ _ hθ (fun q a b => ?_) fun w => ?_
  · rw [GlobalTheory.LatVac.cA_cA, Matrix.of_apply, ← mul_assoc, GlobalTheory.PlaceVec.idemSum_mul_self he]
  by_cases hw : w ∈ latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) (fun _ => True) ∧ IsHalf (cA D e) w
  swap
  · rw [halfInd, if_neg hw, zero_mul, if_neg]
    rintro ⟨h1, h2⟩
    have hN : ∀ PP ∈ R.Pg ∪ R.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hPP h =>
      (hP PP (Finset.mem_union.1 hPP)).2 (by rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h)
    exact hw ⟨mem_latO_of_int hS hT hβV.choose_spec.1 hβW.choose_spec.1 he (Ideal.absNorm_eq_zero_iff.not.2 D.host.ccK_ne_bot)
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D) hN h1 h2, h1⟩
  have hw' : cA D e • w = w := Matrix.ext hw.2
  obtain ⟨M, hM0, u, hu, hwM⟩ := approx_mod (Nat.pos_of_ne_zero hM) hw.1
  obtain ⟨x, rfl⟩ := hsurj M hM0
  have hfr : frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w =
      uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b)) +
        l.M • frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (cA D e • u) := by
    rw [← hw', hwM, smul_add, GlobalTheory.PlaceVec.frMapAdj_add, frMapAdj_half, smul_comm]
    congr 1
    · exact one_smul _ _
    · exact (AddMonoidHom.mk' _ (GlobalTheory.PlaceVec.frMapAdj_add _ _ (R.βV i) (R.βW i))).map_nsmul _ _
  have hred : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) =
      redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b))) := fun PP hPP => by
    rw [hfr]
    have : Ideal.span {(l.M : 𝓞 D.host.E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
    exact GlobalTheory.PlaceVec.redM_add_nsmul PP ((hP PP hPP).1 (this (Ideal.subset_span rfl))) (hφ x).1 (hint u hu)
  rw [halfInd, if_pos hw, one_mul, if_pos ⟨hw.2, hw' ▸ hint w hw.1⟩,
    GlobalTheory.PlaceVec.omegaK_congr _ fun PP h => hred PP (Or.inl h),
    GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ fun PP h => hred PP (Or.inr h), ← (hφ x).2, RingHom.id_apply, ← inversion l φ x]
  refine Finset.sum_congr rfl fun q _ => congrArg _ ?_
  have hY : (Matrix.of fun a b => ((ε : ℤ) : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E)) =
      Matrix.of fun a b => (((ε : ℤ) : D.host.E) / (l.M : D.host.E)) * ι (cSep l • levRep (q b)) a :=
    Matrix.ext fun a b => by simp only [Matrix.of_apply]; ring
  refine Eq.trans ?_ (char_eq (Y := Matrix.of fun a b => ((ε : ℤ) : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E))
    hvac.1 hS hT (GlobalTheory.PlaceVec.idemSum_infPart he) hw.2 hu hwM ((hlat _).2 fun b => ?_)).symm
  · rw [hY, hRat_std hV.1 _ _ _ (by rw [star_div₀, star_intCast, star_natCast]), ← Complex.exp_int_mul]
    congr 1
    have h1 : ∀ c : ℚ, ∀ z : D.host.E, Algebra.trace ℚ D.host.E (D.host.xi0 * ((c : D.host.E) * z)) =
        c * Algebra.trace ℚ D.host.E (D.host.xi0 * z) := fun c z => by
      rw [mul_left_comm, ← Rat.smul_def, map_smul, smul_eq_mul]
    have h2 : ∀ y z, Dw.EF y z = -Dw.EF z y := fun y z => (LinearMap.IsAlt.neg Dw.alt z y).symm
    have h3 : ((pairL (l := l) x (fun b => levRep (q b)) : ℤ) : ℚ) = -(((ε : ℤ) : ℚ) * Algebra.trace ℚ D.host.E (D.host.xi0 *
        ∑ b, (Wc D i).hT ((Wc D i).frame.equivFun.symm (ι (cSep l • levRep (q b)))) ((Wc D i).frame.equivFun.symm (ι (x b))))) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [pairL, Int.cast_sum, Finset.mul_sum, map_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun b _ => by rw [h2, Int.cast_neg, hε]
    have h4 := congrArg (fun z : ℚ => (z : ℂ)) h3
    rw [show (((ε : ℤ) : D.host.E) / (l.M : D.host.E)) = ((((ε : ℤ) : ℚ) / (l.M : ℚ) : ℚ) : D.host.E) by push_cast; rfl, h1]
    push_cast at h4 ⊢
    rw [h4]
    ring
  · have h1 := hι.2.le (LinearMap.mem_range_self ι ((ε : ℤ) • cSep l • levRep (q b)))
    convert h1 using 1
    funext a
    rw [map_zsmul, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul, mul_div_cancel₀ _ hM', Pi.smul_apply, zsmul_eq_mul]

end GlobalTheory.DatumFourierCore

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecFockCore
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.VecFockCore
open GlobalTheory.AdTh.VecFock

open scoped ComplexOrder

theorem vec_fock_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0), VStd D i → IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) ∧ (∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i (sg0 D A)) τ)) (R.vP i t)) ∧ (∀ τ, IsCartanInv (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ)) ∧ (∀ τ, IsCartanInv (gramAt D (Vc D i) τ) 1) ∧ ∀ τ, IsONBasis (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ) (onb (R.MW i (sg0 D A)) τ) ((Wc D i).sig (tauE D τ)).1 := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F h i t hV
  have hθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := h.thP.pt_theta i t 1
    unfold RealDat.ptP pureTensorO at this
    rwa [pureTensorL_one] at this
  refine ⟨hθ, GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ (fun _ => 1) _ _ _ _ _ _ _ _ _ _ (h.thP.vP i t) hθ,
    isCartanInv_cart _, fun τ => ?_, fun τ => isONBasis_onb _ τ _ (h.models.order i τ)⟩
  have : gramAt D (Vc D i) τ = 1 := by
    unfold gramAt
    rw [hV.1]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [this]
  exact ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩

end GlobalTheory.AdTh.VecFockCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM Matrix

namespace GlobalTheory.FlatDegreeCompare

section Lie

variable {R K : Type} [CommRing R] [CommRing K]

def Indep {A : Over (Sp K)} [GrpObj A] {m : ℕ} (x : Fin m → (epsR K ⟶ A)) : Prop :=
  (∀ i, IsTangent (x i)) ∧ ∀ c c' w, IsLieComb c x w → IsLieComb c' x w → c = c'

theorem Indep.of_basis {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] {n : ℕ} {e : Fin n → (epsR K ⟶ A)}
    (he : IsLieBasis e) : Indep e :=
  ⟨he.1, fun c _ w h h' => (he.2 w ((LieComb.lieComb_algebra K A n e he.1).2.1 c w h)).unique h h'⟩

theorem Indep.of_eigBasis {O : Type} [CommRing O] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] {act : OAct O A}
    {χ : O →+* K} {m : ℕ} {x : Fin m → (epsR K ⟶ A)} (h : EigenvectorLieDegree.IsEigBasis act χ x) : Indep x := by
  refine ⟨fun i => (h.1 i).1, fun c c' w hc hc' => (h.2 w ?_).unique hc hc'⟩
  let y : Fin m → Serre.Lie act := fun i => Serre.Lie.mk act (x i) (h.1 i).1
  have hy : ∀ a i, a • y i = χ a • y i := fun a i => Serre.Lie.ext (Over.OverMorphism.ext ((h.1 i).2 a))
  obtain rfl := (Serre.Lie.isLieComb_iff c y w).1 hc
  refine ⟨Serre.Lie.isTangent _, fun a => ?_⟩
  have : a • ∑ i, c i • y i = χ a • ∑ i, c i • y i := by
    rw [Finset.smul_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_comm a, hy, smul_comm]
  exact congrArg (fun z : Serre.Lie act => z.hom.left) this

variable {f : R →+* K} {G : Over (Sp R)} [GrpObj G] {A : Over (Sp K)} [GrpObj A] {φ : A.left ⟶ G.left}

theorem exists_frame [IsLocalRing R] (hG : IsSemiAbelian G) (hφ : IsGrpPullback A G (spMap f) φ) {m : ℕ}
    {x : Fin m → (epsR K ⟶ A)} (hx : ∀ i, IsTangent (x i)) :
    ∃ (n : ℕ) (e : Fin n → (epsR R ⟶ G)) (e' : Fin n → (epsR K ⟶ A)) (P : Matrix (Fin m) (Fin n) K),
      IsLieBasis e ∧ IsLieBasis e' ∧ (∀ j, IsVecOver f φ (e j) (e' j)) ∧ ∀ i, IsLieComb (P i) e' (x i) := by
  have := hG.smooth
  obtain ⟨n, e, he⟩ := Chart.exists_isLieBasis G hG.smooth
  choose e' h _ using fun j => existsUnique_isVecOver hφ.1 (e j)
  have he' := Chart.isLieBasis_baseChange f hφ he h
  choose P hP _ using fun i => he'.2 _ (hx i)
  exact ⟨n, e, e', P, he, he', h, hP⟩

end Lie

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {k : Type} [Field k] [NumberField k]
  {t : SAB H (Sp k)} {m : ℕ} {x : Fin m → (epsR k ⟶ t.G)} {𝔭 : HeightOneSpectrum (𝓞 k)}

end Local

end GlobalTheory.FlatDegreeCompare
end
end

