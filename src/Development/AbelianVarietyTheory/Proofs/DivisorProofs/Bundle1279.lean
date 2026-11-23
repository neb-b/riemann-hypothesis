module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanImageMaxGenEigenspace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1251
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0861
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1253
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1172
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootsOfUnityMapBijectiveOfHenselian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory

theorem rootOfUnity_eq_one_of_map_eq_one {R K : Type} [CommRing R] [IsLocalRing R] [CommRing K]
    [Nontrivial K] (φ : R →+* K) (n : ℕ) (hn : IsUnit (n : R)) (w : R) (hw : w ^ n = 1)
    (hφ : φ w = 1) : w = 1 := by
  have hx : w - 1 ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro h
    have := h.map φ
    rw [map_sub, hφ, map_one, sub_self] at this
    exact not_isUnit_zero this
  have hres : IsLocalRing.residue R w = 1 := by
    rw [← sub_eq_zero, ← map_one (IsLocalRing.residue R), ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hx
  have hS : IsUnit (∑ i ∈ Finset.range n, w ^ i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sum]
    simp only [map_pow, hres, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, _root_.mul_one]
    have := (IsLocalRing.residue_ne_zero_iff_isUnit (n : R)).2 hn
    simpa using this
  have h0 : (∑ i ∈ Finset.range n, w ^ i) * (w - 1) = 0 := by
    rw [geom_sum_mul, hw, sub_self]
  exact sub_eq_zero.1 (hS.mul_right_eq_zero.1 h0)

theorem units_rootOfUnity_map_injective {R K : Type} [CommRing R] [IsLocalRing R] [CommRing K]
    [Nontrivial K] (φ : R →+* K) (n : ℕ) (hn : IsUnit (n : R)) (u v : Rˣ) (hu : u ^ n = 1)
    (hv : v ^ n = 1) (huv : Units.map φ.toMonoidHom u = Units.map φ.toMonoidHom v) : u = v := by
  have hφ : φ (u : R) = φ (v : R) := by
    have := congrArg (fun x : Kˣ => (x : K)) huv
    simpa using this
  have hw : ((u * v⁻¹ : Rˣ) : R) = 1 := by
    apply rootOfUnity_eq_one_of_map_eq_one φ n hn
    · rw [← Units.val_pow_eq_pow_val, mul_pow, hu, inv_pow, hv, inv_one, _root_.mul_one, Units.val_one]
    · rw [Units.val_mul, map_mul, hφ, ← map_mul, Units.mul_inv, map_one]
  exact mul_inv_eq_one.1 (Units.ext hw)

theorem exists_rootOfUnity_lift {R : Type} [CommRing R] [HenselianLocalRing R] (n : ℕ)
    (hn0 : 0 < n) (hn : IsUnit (n : R)) (z : IsLocalRing.ResidueField R) (hz : z ^ n = 1) :
    ∃ a : R, a ^ n = 1 ∧ IsLocalRing.residue R a = z := by
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective z
  have hm : (Polynomial.X ^ n - 1 : Polynomial R).Monic := by
    simpa using Polynomial.monic_X_pow_sub_C (1 : R) hn0.ne'
  have ha₀ : IsUnit a₀ := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    intro h
    rw [h, zero_pow hn0.ne'] at hz
    exact zero_ne_one hz
  obtain ⟨a, ha, hd⟩ := HenselianLocalRing.is_henselian (Polynomial.X ^ n - 1) hm a₀ (by
      rw [← IsLocalRing.residue_eq_zero_iff]
      simp [hz]) (by
      simp [Polynomial.derivative_X_pow]
      exact ⟨hn, ha₀.pow _⟩)
  refine ⟨a, ?_, ?_⟩
  · simpa [sub_eq_zero] using ha
  · rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hd

end GlobalTheory

namespace GlobalTheory

theorem rootsOfUnity_map_bijective_of_henselian : ∀ (R : Type) [CommRing R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)] (K : Type) [Field K] (φ : R →+* K) (n : ℕ), 0 < n →
    IsUnit (n : R) →
    (∀ u v : Rˣ, u ^ n = 1 → v ^ n = 1 → Units.map φ.toMonoidHom u = Units.map φ.toMonoidHom v → u = v) ∧
    ∀ z : Kˣ, z ^ n = 1 → ∃ u : Rˣ, u ^ n = 1 ∧ Units.map φ.toMonoidHom u = z := by
  intro R _ _ _ K _ φ n hn0 hn
  refine ⟨fun u v hu hv huv => units_rootOfUnity_map_injective φ n hn u v hu hv huv, ?_⟩
  haveI : NeZero n := ⟨hn0.ne'⟩
  set ρ := IsLocalRing.residue R
  haveI : NeZero (n : IsLocalRing.ResidueField R) :=
    ⟨by simpa [ρ] using (IsLocalRing.residue_ne_zero_iff_isUnit (n : R)).2 hn⟩
  let f := restrictRootsOfUnity φ n
  let g := restrictRootsOfUnity ρ n
  have hf : ∀ x : rootsOfUnity n R, ((f x : Kˣ) : K) = φ ((x : Rˣ) : R) := fun x => by
    simp [f]
  have hg : ∀ x : rootsOfUnity n R, ((g x : (IsLocalRing.ResidueField R)ˣ) : IsLocalRing.ResidueField R) = ρ ((x : Rˣ) : R) :=
    fun x => by simp [g]
  have ginj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply units_rootOfUnity_map_injective ρ n hn _ _ ((mem_rootsOfUnity _ _).1 x.2)
      ((mem_rootsOfUnity _ _).1 y.2)
    apply Units.ext
    have := congrArg (fun w : rootsOfUnity n (IsLocalRing.ResidueField R) => ((w : (IsLocalRing.ResidueField R)ˣ) : IsLocalRing.ResidueField R)) hxy
    simpa [hg] using this
  have gsurj : Function.Surjective g := by
    intro ζ
    obtain ⟨a, ha, hρ⟩ := exists_rootOfUnity_lift n hn0 hn ((ζ : (IsLocalRing.ResidueField R)ˣ) : IsLocalRing.ResidueField R)
      (by rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 ζ.2, Units.val_one])
    refine ⟨⟨Units.ofPowEqOne a n ha hn0.ne', (mem_rootsOfUnity _ _).2 (Units.ext (by simp [ha]))⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [hg]
    simpa using hρ
  have hcardR : Nat.card (rootsOfUnity n R) = n := by
    rw [Nat.card_eq_of_bijective g ⟨ginj, gsurj⟩, HasEnoughRootsOfUnity.natCard_rootsOfUnity]
  have finj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply units_rootOfUnity_map_injective φ n hn _ _ ((mem_rootsOfUnity _ _).1 x.2)
      ((mem_rootsOfUnity _ _).1 y.2)
    apply Units.ext
    have := congrArg (fun w : rootsOfUnity n K => ((w : Kˣ) : K)) hxy
    simpa [hf] using this
  have fbij : Function.Bijective f :=
    finj.bijective_of_nat_card_le (by rw [hcardR]; exact card_rootsOfUnity K n)
  intro z hz
  obtain ⟨x, hx⟩ := fbij.2 ⟨z, (mem_rootsOfUnity _ _).2 hz⟩
  refine ⟨x, (mem_rootsOfUnity _ _).1 x.2, ?_⟩
  apply Units.ext
  have := congrArg (fun w : rootsOfUnity n K => ((w : Kˣ) : K)) hx
  simpa [hf] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowEigensystemCarriedByFiniteType
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.Div

theorem span_range_comp_basis {K V W ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (b : Module.Basis ι K V) :
    Submodule.span ℂ (Set.range fun k => j (b k)) = Submodule.span ℂ (Set.range j) := by
  refine le_antisymm (Submodule.span_mono (Set.range_subset_iff.2 fun k => ⟨b k, rfl⟩)) ?_
  rw [Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  have hv : v ∈ Submodule.span K (Set.range b) := b.span_eq ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem y hy => obtain ⟨k, rfl⟩ := hy; exact Submodule.subset_span ⟨k, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hy

theorem exists_sys_of_mem_span {K V W I ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    [Finite ι] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (b : Module.Basis ι K V) (op : I → Module.End K V)
    (opC : I → Module.End ℂ W) (Z : Submodule K V) (hli : LinearIndependent ℂ (fun k => j (b k)))
    (hsp : Submodule.span ℂ (Set.range j) = ⊤) (hcomm : ∀ i v, j (op i v) = opC i (j v))
    (hpc : Formalism.L2.Col.PairComm op) (hso : Formalism.L2.Col.SplitOver op) (x : I → ℂ) (u : W)
    (hu : ∀ i, opC i u = x i • u) (hu0 : u ≠ 0) (huZ : u ∈ Submodule.span ℂ (j '' (Z : Set V))) :
    ∃ s : I → K, x = (fun i => σ (s i)) ∧
      Formalism.L2.Col.eigAt opC x = Submodule.span ℂ (j '' (Formalism.L2.Col.eigAt op s : Set V)) ∧
      ∃ f, f ≠ 0 ∧ f ∈ Z ∧ f ∈ Formalism.L2.Col.eigAt op s := by
  have hsp' : Submodule.span ℂ (Set.range fun k => j (b k)) = ⊤ := (span_range_comp_basis σ j b).trans hsp
  have key := GlobalTheory.span_image_eigAt_of_basis σ j b op opC hli hsp' hcomm
  have hmem : u ∈ Formalism.L2.Col.eigAt opC x := Formalism.L2.Col.mem_eigAt_of_forall_apply hu
  have hocc : Formalism.L2.Col.Occurs opC x := fun hbot => hu0 ((Submodule.eq_bot_iff _).1 hbot u hmem)
  obtain ⟨s, _, rfl⟩ := key.2.2 hpc hso x hocc
  refine ⟨s, rfl, (key.1 s).symm, ?_⟩
  have hin : u ∈ Submodule.span ℂ (j '' ((Z ⊓ Formalism.L2.Col.eigAt op s : Submodule K V) : Set V)) := by
    rw [← GlobalTheory.span_image_inf_of_linearIndependent σ j b hli]
    exact ⟨huZ, (key.1 s) ▸ hmem⟩
  by_contra hcon
  push_neg at hcon
  apply hu0
  have hle : Submodule.span ℂ (j '' ((Z ⊓ Formalism.L2.Col.eigAt op s : Submodule K V) : Set V)) ≤ ⊥ := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    by_cases hy0 : y = 0
    · subst hy0; simp
    · exact absurd hy.2 (hcon y hy0 hy.1)
  exact (Submodule.mem_bot ℂ).1 (hle hin)

theorem map_le_span_image {K V W H : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup H] [Module ℂ H] {σ : K →+* ℂ} (j : V →ₛₗ[σ] W) (Θ : H →ₗ[ℂ] W) (E : Submodule ℂ H)
    (A B : Submodule K V) (h : ∀ v ∈ E, Θ v ∈ Submodule.span ℂ (j '' (A : Set V))) (hAB : A ≤ B) :
    E.map Θ ≤ Submodule.span ℂ (j '' (B : Set V)) := by
  rw [Submodule.map_le_iff_le_comap]
  intro v hv
  exact Submodule.span_mono (Set.image_mono hAB) (h v hv)


set_option maxHeartbeats 400000 in
theorem carries_of_eEc_ne_bot : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → R.PGEquiv F → Nonempty A3.fam3.base3.Ix → (∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hLI hOk hCW hEx hSch hTw hHk hPG hIx c hc
  obtain ⟨Tc, hTc, hx⟩ := _root_.GlobalTheory.UpSystem.up_sys R F hLI hOk hCW hEx hSch hTw hHk
  obtain ⟨x, hxc⟩ := hx c
  by_cases h0 : ∀ w ∈ R.EEc c, LinearMap.adjoint (R.Th A3.A.μ0) w = 0
  · obtain ⟨p⟩ := hIx
    refine ⟨p, hc, ?_⟩
    rewrite [Submodule.map_le_iff_le_comap]
    intro w hw
    have h := h0 w hw
    simp only [Submodule.mem_comap, h, Submodule.zero_mem]
  push_neg at h0
  obtain ⟨w, hw, hne⟩ := h0
  let b := (A3.A.fam.R A3.A.μ0).S.basis
  let j := R.jX A3.A.μ0
  let op := (A3.rowI A3.A.μ0).opAll
  have hmodels := hCW.base.models
  have hjX := GlobalTheory.OneFormTest.model_jX R.toRealDat hmodels.HX hmodels.jX A3.A.μ0
  have hExt := (GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.R A3.A.μ0).pres).2.1
  have h2 : ∀ f, (R.HX A3.A.μ0).e (R.jX A3.A.μ0 f) = (R.B.R A3.A.μ0).pres.extL f := hmodels.jX A3.A.μ0
  have hli0 : LinearIndependent ℂ (fun k => (R.B.R A3.A.μ0).pres.extL ((A3.A.MtildeCSD A3.A.μ0).basis k)) := hExt.1
  have hli : LinearIndependent ℂ (fun k => j (b k)) := by
    refine LinearIndependent.of_comp (R.HX A3.A.μ0).e ?_
    have h3 : ((R.HX A3.A.μ0).e ∘ fun k => j (b k)) =
        fun k => (R.B.R A3.A.μ0).pres.extL ((A3.A.MtildeCSD A3.A.μ0).basis k) := funext fun k => h2 _
    rewrite [h3]
    exact hli0
  have hcomm : ∀ i f, j (op i f) = Tc i (j f) := hTc
  have hpc : Formalism.L2.Col.PairComm op := (hOk.what₂ A3.A.μ0).comm
  have hso : Formalism.L2.Col.SplitOver op := by
    rintro (i | k)
    · exact (hOk.ok2.what₂ A3.A.μ0).split i
    · exact (hOk.what₂ A3.A.μ0).split k
  have hZ := (_root_.GlobalTheory.AdjBlockSpan.range_adjoint_le_span_good_block R F hLI hOk hCW hEx hSch hPG).1 A3.A.μ0
  obtain ⟨s', hxs, heig, f, hf0, hfZ, hfE⟩ := exists_sys_of_mem_span D.what₂.embLL j b op Tc
    ((A3.A.fam.R A3.A.μ0).ZHg A3.A.X) hli hjX.2.2 hcomm hpc hso x (LinearMap.adjoint (R.Th A3.A.μ0) w) (hxc w hw) hne
    (hZ ⟨w, rfl⟩)
  obtain ⟨p, hp⟩ := GlobalTheory.Div.exists_ix_of_mem_eigAt A3 hOk s' f hf0 hfZ hfE
  refine ⟨p, hc, map_le_span_image j (LinearMap.adjoint (R.Th A3.A.μ0)) (R.EEc c) (Formalism.L2.Col.eigAt op s')
    ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1)
    (fun v hv => heig.le (Formalism.L2.Col.mem_eigAt_of_forall_apply (hxc v hv))) (Formalism.L2.Col.eigAt_le_eigSum hp)⟩

end GlobalTheory.Div
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatMatrixCoefficientCompactSupportFin
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny
open MeasureTheory

noncomputable section

namespace GlobalTheory.SchrSuppFin

theorem exists_nhds_translate_eq {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [NonarchimedeanAddGroup V] {f : V → ℂ} (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    ∃ U ∈ nhds (0 : V), ∀ u ∈ U, ∀ z, f (z + u) = f z := by
  have hW : ∀ x : V, ∃ W : OpenAddSubgroup V, ∀ w ∈ (W : Set V), f (x + w) = f x := by
    intro x
    have h1 : {w : V | f (x + w) = f x} ∈ nhds (0 : V) := by
      have h2 := (hf.comp_continuous (show Continuous (fun w : V => x + w) from continuous_const.add continuous_id)).eventually_eq 0
      simp only [Function.comp, add_zero] at h2
      exact h2
    obtain ⟨W, hW⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ h1
    exact ⟨W, fun w hw => hW hw⟩
  choose W hW using hW
  obtain ⟨t, -, ht⟩ := hc.isCompact.elim_nhds_subcover (fun x => {z : V | z - x ∈ (W x : Set V)}) (fun x _ => by
    refine (continuous_sub_right x).continuousAt.preimage_mem_nhds ?_
    simpa using (W x).isOpen.mem_nhds (W x).zero_mem)
  refine ⟨⋂ x ∈ t, (W x : Set V), (Filter.biInter_finset_mem t).2 fun x _ => (W x).isOpen.mem_nhds (W x).zero_mem,
    fun u hu z => ?_⟩
  simp only [Set.mem_iInter] at hu
  by_cases hz : ∃ x ∈ t, z - x ∈ (W x : Set V)
  · obtain ⟨x, hx, hzx⟩ := hz
    have e1 := hW x (z - x) hzx
    have e2 := hW x (z + u - x) (by
      rw [show z + u - x = (z - x) + u by abel]; exact (W x).add_mem hzx (hu x hx))
    rw [show x + (z - x) = z by abel] at e1
    rw [show x + (z + u - x) = z + u by abel] at e2
    rw [e1, e2]
  · push_neg at hz
    have h1 : z ∉ tsupport f := fun h => by
      obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp (ht h)
      exact hz x hx hzx
    have h2 : z + u ∉ tsupport f := fun h => by
      obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp (ht h)
      refine hz x hx ?_
      have := (W x).sub_mem hzx (hu x hx)
      rwa [show z + u - x - u = z - x by abel] at this
    rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]

theorem nhdsNE_neBot {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) : (nhdsWithin (0 : Fv F v) {0}ᶜ).NeBot := by
  refine ⟨fun h => ?_⟩
  have hopen : IsOpen ({0} : Set (Fv F v)) := (isOpen_singleton_iff_punctured_nhds _).2 h
  haveI := discreteTopology_of_isOpen_singleton_zero hopen
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have hO : IsCompact ((v.adicCompletionIntegers F : Set (Fv F v))) := isCompact_iff_compactSpace.2 inferInstance
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective
  have hinf : ((v.adicCompletionIntegers F : Set (Fv F v))).Infinite :=
    Set.infinite_of_injective_forall_mem (Nat.cast_injective (R := Fv F v)) fun n => natCast_mem _ n
  exact hinf (hO.finite_of_discrete)

end GlobalTheory.SchrSuppFin

namespace GlobalTheory.SchrSuppFin

theorem support_compact : ∀ {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (ψ₀ : AddChar (Fv F v) ℂ) (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : MeasureTheory.Measure (κ → Fv F v))
    [μ.IsAddHaarMeasure], Continuous ψ₀ →
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x * y) = 1) → x ∈ v.adicCompletionIntegers F) →
    ∀ φ ∈ SB (κ → Fv F v), ∀ g ∈ SB (κ → Fv F v),
    ∃ C : Set ((κ → Fv F v) × (κ → Fv F v)), IsCompact C ∧
      ∀ w, ∫ y, schr ψ₀ w φ y * (starRingEnd ℂ) (g y) ∂μ ≠ 0 → w ∈ C := by
  intro F _ _ v ψ₀ κ _ _ _ μ _ hψ hcond φ hφ g hg
  classical
  obtain ⟨hφl, hφc⟩ := hφ
  obtain ⟨hgl, hgc⟩ := hg
  obtain ⟨Uφ, hUφ, hφU⟩ := exists_nhds_translate_eq hφl hφc
  obtain ⟨Ug, hUg, hgU⟩ := exists_nhds_translate_eq hgl hgc
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have hO : IsCompact ((v.adicCompletionIntegers F : Set (Fv F v))) := isCompact_iff_compactSpace.2 inferInstance
  have hP : ∀ᶠ s in nhds (0 : Fv F v), ∀ y ∈ (v.adicCompletionIntegers F : Set (Fv F v)), ∀ i : κ,
      (Pi.single i (s * y) : κ → Fv F v) ∈ Uφ ∩ Ug := by
    refine hO.eventually_forall_of_forall_eventually fun y _ => ?_
    refine Filter.eventually_all.2 fun i => ?_
    have hc : Continuous fun p : Fv F v × Fv F v => (Pi.single i (p.1 * p.2) : κ → Fv F v) :=
      (continuous_single i).comp continuous_mul
    have hmem : Uφ ∩ Ug ∈ nhds ((fun p : Fv F v × Fv F v => (Pi.single i (p.1 * p.2) : κ → Fv F v)) (0, y)) := by
      simpa using Filter.inter_mem hUφ hUg
    exact hc.continuousAt.preimage_mem_nhds hmem
  haveI := nhdsNE_neBot v
  obtain ⟨t, ht, ht0⟩ := ((hP.filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ))).and
    (self_mem_nhdsWithin (s := ({0}ᶜ : Set (Fv F v))))).exists
  have ht0' : t ≠ 0 := ht0
  refine ⟨((fun p : (κ → Fv F v) × (κ → Fv F v) => p.1 - p.2) '' (tsupport φ ×ˢ tsupport g)) ×ˢ
    Set.pi Set.univ (fun _ => (fun y => t⁻¹ * y) '' (v.adicCompletionIntegers F : Set (Fv F v))), ?_, ?_⟩
  · exact ((hφc.isCompact.prod hgc.isCompact).image continuous_sub).prod
      (isCompact_univ_pi fun _ => hO.image (continuous_const_mul _))
  · rintro ⟨a, b⟩ hne
    have key : ∀ u ∈ Uφ ∩ Ug, ψ₀ (u ⬝ᵥ b) = 1 := by
      intro u hu
      have hG : ∀ y, schr ψ₀ (a, b) φ (y + u) * (starRingEnd ℂ) (g (y + u)) =
          ψ₀ (u ⬝ᵥ b) * (schr ψ₀ (a, b) φ y * (starRingEnd ℂ) (g y)) := by
        intro y
        simp only [schr]
        rw [show y + u + a = (y + a) + u by abel, hφU u hu.1, hgU u hu.2, add_dotProduct,
          show y ⬝ᵥ b + u ⬝ᵥ b + ⅟(2 : Fv F v) * (a ⬝ᵥ b) = u ⬝ᵥ b + (y ⬝ᵥ b + ⅟(2 : Fv F v) * (a ⬝ᵥ b)) by ring,
          AddChar.map_add_eq_mul]
        ring
      have e := integral_add_right_eq_self (μ := μ)
        (fun y => schr ψ₀ (a, b) φ y * (starRingEnd ℂ) (g y)) u
      simp only [hG] at e
      rw [integral_const_mul] at e
      have h0 : (ψ₀ (u ⬝ᵥ b) - 1) * ∫ y, schr ψ₀ (a, b) φ y * (starRingEnd ℂ) (g y) ∂μ = 0 := by
        rw [sub_mul, e]; ring
      exact sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_right hne)
    refine ⟨?_, ?_⟩
    · have hex : ∃ y, schr ψ₀ (a, b) φ y * (starRingEnd ℂ) (g y) ≠ 0 := by
        by_contra h
        push_neg at h
        exact hne (by simp [h])
      obtain ⟨y, hy⟩ := hex
      have h1 : φ (y + a) ≠ 0 := fun h => hy (by simp [schr, h])
      have h2 : g y ≠ 0 := fun h => hy (by simp [h])
      exact ⟨(y + a, y), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, by simp⟩
    · intro i _
      have hb : t * b i ∈ v.adicCompletionIntegers F := hcond _ fun y hy => by
        have := key _ (ht y hy i)
        rwa [single_dotProduct, show t * y * b i = t * b i * y by ring] at this
      exact ⟨t * b i, hb, by field_simp⟩

end GlobalTheory.SchrSuppFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTorusElementInvFinitePartOneDualFrameEigen
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TorusInv

theorem dual_mul_compl {R : Type} [CommRing R] {m r : ℕ} (X Y : Matrix (Fin m) (Fin r) R)
    (X' Y' : Matrix (Fin r) (Fin m) R) (xx : X' * X = 0) (yy : Y' * Y = 0) (xy : X' * Y = 1) (yx : Y' * X = 1) :
    X' * (1 - X * Y' - Y * X') = 0 ∧ Y' * (1 - X * Y' - Y * X') = 0 := by
  constructor
  · rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, xx, xy]; simp
  · rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, yx, yy]; simp

theorem mapped {E : Type} [CommRing E] (f : E →+* ℂ) {m r : ℕ} (X Y : Matrix (Fin m) (Fin r) E)
    (X' Y' : Matrix (Fin r) (Fin m) E) (xx : X' * X = 0) (yy : Y' * Y = 0) (xy : X' * Y = 1) (yx : Y' * X = 1)
    (t : Fin r → ℝ) (ht : ∀ i, 0 < t i) (A B : Matrix (Fin m) (Fin m) ℂ)
    (hX : A * X.map f = X.map f * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)))
    (hY : A * Y.map f = Y.map f * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹))
    (hz : ∀ z : Fin m → E, X' *ᵥ z = 0 → Y' *ᵥ z = 0 → A *ᵥ (fun i => f (z i)) = fun i => f (z i))
    (hAB : A * B = 1) :
    Y'.map f * B = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹) * Y'.map f ∧
    X'.map f * B = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)) * X'.map f ∧
    (1 - X * Y' - Y * X').map f * B = (1 - X * Y' - Y * X').map f := by
  have hP : (1 - X * Y' - Y * X').map f = 1 - X.map f * Y'.map f - Y.map f * X'.map f := by
    rw [Matrix.map_sub _ (map_sub f), Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul,
      Matrix.map_one _ (map_zero f) (map_one f)]
  obtain ⟨k1, k2⟩ := dual_mul_compl X Y X' Y' xx yy xy yx
  have hA : A * (1 - X * Y' - Y * X').map f = (1 - X * Y' - Y * X').map f := by
    ext i j
    have := hz (fun k => (1 - X * Y' - Y * X' : Matrix (Fin m) (Fin m) E) k j)
      (by funext a; exact congrFun (congrFun k1 a) j) (by funext a; exact congrFun (congrFun k2 a) j)
    exact congrFun this i
  have hne : ∀ i, ((t i : ℝ) : ℂ) ≠ 0 := fun i => Complex.ofReal_ne_zero.2 (ht i).ne'
  rw [hP] at hA ⊢
  refine _root_.GlobalTheory.torus_dual_frame_rows_eigen ℂ m r (X.map f) (Y.map f) (X'.map f) (Y'.map f) _ _ A B ?_ ?_ ?_ ?_ ?_ ?_ hX hY hA hAB
  · rw [← Matrix.map_mul, xx, Matrix.map_zero _ (map_zero f)]
  · rw [← Matrix.map_mul, yy, Matrix.map_zero _ (map_zero f)]
  · rw [← Matrix.map_mul, xy, Matrix.map_one _ (map_zero f) (map_one f)]
  · rw [← Matrix.map_mul, yx, Matrix.map_one _ (map_zero f) (map_one f)]
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; exact mul_inv_cancel₀ (hne i)
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; exact inv_mul_cancel₀ (hne i)

theorem torus_inv : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (t : Fin r → ℝ), (∀ i, 0 < t i) → ∀ a : GA D V, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram X Y t a → (Formalism.L2.Theta.mt V a⁻¹).map (finPart D) = 1 ∧ ∀ τ, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram).map (tauE D τ) * Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹) * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram).map (tauE D τ) ∧ (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram).map (tauE D τ) * Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)) * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram).map (tauE D τ) ∧ (1 - X * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) - Y * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram)).map (tauE D τ) * Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) = (1 - X * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) - Y * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram)).map (tauE D τ) := by
  intro D θ hθ V r X Y hW t ht a ha
  obtain ⟨hf, hr⟩ := _root_.GlobalTheory.TorusDict.torus_dict D θ hθ V r X Y t a ha
  have h1 : Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V a⁻¹ = 1 := by simp [Formalism.L2.Theta.mt]
  refine ⟨?_, fun τ => ?_⟩
  · have h2 := congrArg (fun M => Matrix.map M (finPart D)) h1
    rw [Matrix.map_mul, hf, Matrix.one_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
    exact h2
  · obtain ⟨hX, hY, hz⟩ := hr τ
    have hAB : Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) *
        Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) = 1 := by
      have h3 : Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V a⁻¹) =
          Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) * Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a⁻¹) :=
        Matrix.map_mul (f := (θ τ).comp (infPart D))
      rw [← h3, h1]
      exact Matrix.map_one _ (map_zero ((θ τ).comp (infPart D))) (map_one ((θ τ).comp (infPart D)))
    exact mapped (tauE D τ) X Y _ _ hW.xx hW.yy hW.xy (_root_.GlobalTheory.WittFrame.yx_eq_one D V r X Y hW) t ht _ _ hX hY hz hAB

end GlobalTheory.TorusInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPolynomialsToProductVariablesCompPderivStatement
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorPolynomialsToProductVariables_comp_pderiv : ∀ (W Λ : Type) [Fintype W] [DecidableEq W] (w : W) (l : Λ),
    GlobalTheory.CCRFock.polMap W Λ ∘ₗ GlobalTheory.RealLift.atPl (V := fun _ : W => MvPolynomial Λ ℂ) w
                 (MvPolynomial.pderiv l).toLinearMap =
      (MvPolynomial.pderiv (w, l)).toLinearMap ∘ₗ GlobalTheory.CCRFock.polMap W Λ := by
  first | exact @GlobalTheory.CCRFock.polMap_comp_atPl_pderiv | exact GlobalTheory.CCRFock.polMap_comp_atPl_pderiv | (intros; apply GlobalTheory.CCRFock.polMap_comp_atPl_pderiv <;> assumption)
end

