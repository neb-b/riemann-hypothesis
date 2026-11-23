module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0565
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0660
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0594
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0561
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0638
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0655
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0639
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0631
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0451

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorLiftOfAnalyticThickening
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem exists_tensorLift_of_DObj {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam Empty g Λ} (K₀ : Charts F₀) {R : Type} [CommRing R]
    [Algebra ℂ R] (et : Hol F₀.V →ₐ[ℂ] R) (M : Ideal R) (S : K₀.DObj (et : Hol F₀.V →+* R) M) :
    ∃ ψ : R ⊗[ℂ] Hol (K₀.W S.T.k) →+* S.T.C, ∀ (d : R) (h : Hol (K₀.W S.T.k)),
      ψ (d ⊗ₜ[ℂ] h) = algebraMap R S.T.C d * S.T.ρ h := by
  letI : Algebra ℂ S.T.C := ((algebraMap R S.T.C).comp (algebraMap ℂ R)).toAlgebra
  let fR : R →ₐ[ℂ] S.T.C := { algebraMap R S.T.C with commutes' := fun _ ↦ rfl }
  let fH : Hol (K₀.W S.T.k) →ₐ[ℂ] S.T.C :=
    { S.T.ρ with
      commutes' := fun a ↦ by
        have h1 : algebraMap ℂ (Hol (K₀.W S.T.k)) a = K₀.cst S.T.k (algebraMap ℂ (Hol F₀.V) a) :=
          ((Hol.comap Prod.fst (fun _ _ ↦ analyticAt_fst) (K₀.base S.T.k)).commutes a).symm
        change S.T.ρ (algebraMap ℂ (Hol (K₀.W S.T.k)) a) = algebraMap R S.T.C (algebraMap ℂ R a)
        rw [h1, S.T.ρ_cst, S.compat]
        change algebraMap R S.T.C (et (algebraMap ℂ (Hol F₀.V) a)) = _
        rw [et.commutes] }
  refine ⟨(Algebra.TensorProduct.lift fR fH (fun _ _ ↦ Commute.all _ _)).toRingHom, fun d h ↦ ?_⟩
  exact Algebra.TensorProduct.lift_tmul _ _ _ d h

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeBaseChangeOfIdem
section
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct Coalgebra Bialgebra GlobalTheory.PDiv

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDivGroup.IdemSplit

theorem finrank_range_baseChange_of_idem {R S M : Type} [CommRing R] [CommRing S] [Algebra R S]
    [StrongRankCondition R] [StrongRankCondition S] [AddCommGroup M] [Module R M]
    (e : M →ₗ[R] M) (he : e ∘ₗ e = e) [Module.Free R (LinearMap.range e)] :
    Module.finrank S (LinearMap.range (e.baseChange S)) =
      Module.finrank R (LinearMap.range e) := by
  let r : M →ₗ[R] LinearMap.range e := e.rangeRestrict
  let i : LinearMap.range e →ₗ[R] M := (LinearMap.range e).subtype
  have hri : r ∘ₗ i = LinearMap.id := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    obtain ⟨y, hy⟩ := x.2
    change e x.1 = x.1
    rw [← hy]
    exact LinearMap.congr_fun he y
  have hir : e = i ∘ₗ r := LinearMap.ext fun _ => rfl
  have hS : r.baseChange S ∘ₗ i.baseChange S = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hri, LinearMap.baseChange_id]
  have hsurj : Function.Surjective (r.baseChange S) := fun x =>
    ⟨i.baseChange S x, LinearMap.congr_fun hS x⟩
  have hinj : Function.Injective (i.baseChange S) := fun x y hxy => by
    have := congrArg (r.baseChange S) hxy
    rwa [← LinearMap.comp_apply, hS, ← LinearMap.comp_apply, hS] at this
  have h2 : e.baseChange S = i.baseChange S ∘ₗ r.baseChange S := by
    rw [← LinearMap.baseChange_comp, ← hir]
  rw [h2, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 hsurj),
    LinearMap.finrank_range_of_inj hinj, Module.finrank_baseChange]

def quotEquivRange {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (f : A →ₐ[R] A)
    (I : Ideal A) (h : RingHom.ker f = I) : (A ⧸ I) ≃ₗ[R] LinearMap.range f.toLinearMap :=
  (Submodule.Quotient.restrictScalarsEquiv R I).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (by ext x; simp [← h]) ≪≫ₗ
    LinearMap.quotKerEquivRange f.toLinearMap

end GlobalTheory.PDivGroup.IdemSplit

namespace GlobalTheory.PDivGroup.IdemSplit

open GlobalTheory.PDivGroup.KerGrp

theorem exists_of_family {p : ℕ} {k : Type} [CommRing k] (G : PDivGroup p k)
    (v : G ⟶ G) (h₀ : ℕ) (B : ℕ → Type) [∀ n, CommRing (B n)] [∀ n, HopfAlgebra k (B n)]
    [∀ n, Module.Projective k (B n)]
    (π : ∀ n, G.A n →ₐc[k] B n) (hπ : ∀ n, Function.Surjective (π n))
    (hk : ∀ n, RingHom.ker (π n) = kerIdeal (v.app n))
    (h : ∀ (n : ℕ) (q : PrimeSpectrum k), Module.rankAtStalk (B n) q = p ^ (n * h₀)) :
    ∃ (K : PDivGroup p k) (i : K ⟶ G), ∀ n : ℕ, Function.Surjective (i.app n) ∧
      RingHom.ker (i.app n) = kerIdeal (v.app n) := by
  haveI : ∀ n, IsCocomm k (B n) := fun n => isCocomm_of_surjective (π n) (hπ n)
  have hle : ∀ n, RingHom.ker (π (n + 1)) ≤ RingHom.ker ((π n).comp (G.res n)) := fun n a ha => by
    have : G.res n a ∈ RingHom.ker (π n) := by
      rw [hk, ← map_res_kerIdeal]
      rw [hk] at ha
      exact Ideal.mem_map_of_mem (G.res n : G.A (n + 1) →ₐ[k] G.A n) ha
    exact this
  let r := fun n => liftSurj (π (n + 1)) (hπ (n + 1)) ((π n).comp (G.res n)) (hle n)
  have hr : ∀ n a, r n (π (n + 1) a) = π n (G.res n a) := fun n a => liftSurj_apply ..
  let K : PDivGroup p k :=
    { height := h₀
      A := B
      finite := fun n => Module.Finite.of_surjective (π n : G.A n →ₗ[k] B n) (hπ n)
      rank_eq := h
      res := r
      res_surjective := fun n b => by
        obtain ⟨c, rfl⟩ := hπ n b
        obtain ⟨a, rfl⟩ := G.res_surjective n c
        exact ⟨_, hr n a⟩
      ker_res := fun n => by
        rw [← map_torsionIdeal (hπ (n + 1)), ← G.ker_res]
        refine le_antisymm (fun b hb => ?_) (Ideal.map_le_iff_le_comap.2 fun a ha => ?_)
        · obtain ⟨a, rfl⟩ := hπ _ b
          have h1 : G.res n a ∈ RingHom.ker (π n) := (hr n a).symm.trans hb
          rw [hk, ← map_res_kerIdeal] at h1
          obtain ⟨c, hc, e⟩ := (Ideal.mem_map_iff_of_surjective
            (G.res n : G.A (n + 1) →ₐ[k] G.A n) (G.res_surjective n)).1 h1
          rw [← hk] at hc
          have hc' : π (n + 1) c = 0 := hc
          have e' : G.res n c = G.res n a := e
          have h2 : a - c ∈ RingHom.ker (G.res n) := by
            rw [RingHom.mem_ker, map_sub, e', sub_self]
          have h3 : π (n + 1) a = π (n + 1) (a - c) := by rw [map_sub, hc', sub_zero]
          rw [h3]
          exact Ideal.mem_map_of_mem (π (n + 1) : G.A (n + 1) →ₐ[k] B (n + 1)) h2
        · have ha' : G.res n a = 0 := ha
          change r n (π (n + 1) a) = 0
          rw [hr, ha', map_zero] }
  exact ⟨K, ⟨π, fun n => BialgHom.ext fun a => hr n a⟩, fun n => ⟨hπ n, hk n⟩⟩

end GlobalTheory.PDivGroup.IdemSplit

namespace GlobalTheory.PDivGroup.IdemSplit

theorem baseChangeMap_zero {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (O' : Type) [CommRing O']
    [Algebra O O'] (G H : PDivGroup p O) : baseChangeMap O' (0 : G ⟶ H) = 0 := by
  have h := baseChangeMap_add O' (0 : G ⟶ H) 0
  rw [add_zero] at h
  exact (add_eq_left.1 h.symm)

theorem bcMap_toLinearMap {O : Type} [CommRing O] (O' : Type) [CommRing O'] [Algebra O O']
    {A : Type} [CommRing A] [Bialgebra O A] (f : A →ₐc[O] A) :
    ((bcMap O' f : O' ⊗[O] A →ₐ[O'] O' ⊗[O] A)).toLinearMap =
      ((f : A →ₐ[O] A).toLinearMap).baseChange O' := by
  refine LinearMap.ext fun x => ?_
  induction x with
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | tmul r a => exact bcMap_tmul f r a

variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O]

theorem idempotent_split_of_isLocalRing (G : PDivGroup p O) (u : G ⟶ G) (hu : u ≫ u = u) :
    ∃ (H : PDivGroup p O) (i : H ⟶ G) (q : G ⟶ H), i ≫ q = 𝟙 H ∧ q ≫ i = u := by
  set v : G ⟶ G := 𝟙 G - u with hv
  have huv : u + v = 𝟙 G := add_sub_cancel u (𝟙 G)
  have h1 : u ≫ v = 0 := by rw [hv, Preadditive.comp_sub, hu, Category.comp_id, sub_self]
  have h2 : v ≫ u = 0 := by rw [hv, Preadditive.sub_comp, hu, Category.id_comp, sub_self]
  have hker : ∀ n, RingHom.ker (u.app n) = kerIdeal (v.app n) :=
    ker_app_eq_kerIdeal_of_idempotents p O G u v huv h1 h2

  let k := IsLocalRing.ResidueField O
  let uk := baseChangeMap k u
  let vk := baseChangeMap k v
  have hF : ∀ {X Y Z : PDivGroup p O} (f : X ⟶ Y) (g : Y ⟶ Z),
      baseChangeMap k (f ≫ g) = baseChangeMap k f ≫ baseChangeMap k g := fun f g =>
    (baseChangeFunctor p O k).map_comp f g
  have hI : baseChangeMap k (𝟙 G) = 𝟙 (G.baseChange k) := (baseChangeFunctor p O k).map_id G
  have hvuk : vk + uk = 𝟙 _ := by rw [← baseChangeMap_add, add_comm, huv, hI]
  have huvk : uk + vk = 𝟙 _ := by rw [add_comm]; exact hvuk
  have h1k : uk ≫ vk = 0 := by rw [← hF, h1, baseChangeMap_zero]
  have h2k : vk ≫ uk = 0 := by rw [← hF, h2, baseChangeMap_zero]
  obtain ⟨h₀, hrk⟩ := kerIdeal_finrank_eq_pow_of_idempotent p k (G.baseChange k) vk uk
    hvuk h2k h1k
  have hkerk : ∀ n, RingHom.ker (uk.app n) = kerIdeal (vk.app n) :=
    ker_app_eq_kerIdeal_of_idempotents p k (G.baseChange k) uk vk huvk h1k h2k

  let e : ∀ n, G.A n →ₗ[O] G.A n := fun n => ((u.app n : G.A n →ₐ[O] G.A n)).toLinearMap
  have he : ∀ n, e n ∘ₗ e n = e n := fun n => LinearMap.ext fun a =>
    DFunLike.congr_fun (congrArg (fun w : G ⟶ G => w.app n) hu) a
  have hproj : ∀ n, Module.Projective O (LinearMap.range (e n)) := fun n =>
    Module.Projective.of_split (LinearMap.range (e n)).subtype (e n).rangeRestrict
      (LinearMap.ext fun x => Subtype.ext (by
        obtain ⟨y, hy⟩ := x.2
        change e n x.1 = x.1
        rw [← hy]
        exact LinearMap.congr_fun (he n) y))
  have hfin : ∀ n, Module.Finite O (LinearMap.range (e n)) := fun n =>
    Module.Finite.of_surjective (e n).rangeRestrict (LinearMap.surjective_rangeRestrict _)
  have hfree : ∀ n, Module.Free O (LinearMap.range (e n)) := fun n =>
    Module.free_of_flat_of_isLocalRing
  let B := fun n => G.A n ⧸ kerIdeal (v.app n)
  have hHopf : ∀ n, (kerIdeal (v.app n)).IsHopfIdeal O := fun n =>
    GlobalTheory.PDiv.isHopfIdeal_kerIdeal_of_bialgHom O _ _ (v.app n)
  let eqv : ∀ n, B n ≃ₗ[O] LinearMap.range (e n) := fun n =>
    quotEquivRange (u.app n : G.A n →ₐ[O] G.A n) _ (hker n)
  have hBproj : ∀ n, Module.Projective O (B n) := fun n =>
    Module.Projective.of_equiv (eqv n).symm
  have hrank : ∀ n, Module.finrank O (B n) = p ^ (n * h₀) := fun n => by
    rw [(eqv n).finrank_eq, ← finrank_range_baseChange_of_idem (S := k) (e n) (he n),
      ← bcMap_toLinearMap, ← (quotEquivRange _ _ (hkerk n)).finrank_eq]
    exact hrk n
  have hBrank : ∀ (n : ℕ) (q : PrimeSpectrum O), Module.rankAtStalk (B n) q = p ^ (n * h₀) :=
    fun n q => by
      haveI := Module.Free.of_equiv (eqv n).symm
      rw [Module.rankAtStalk_eq_finrank_of_free, hrank]
      rfl
  obtain ⟨K, i, hi⟩ := exists_of_family G v h₀ B
    (fun _ => Bialgebra.Quotient.mkBialgHom _) (fun _ => Ideal.Quotient.mk_surjective)
    (fun _ => Ideal.ext fun _ => Ideal.Quotient.eq_zero_iff_mem) hBrank
  obtain ⟨hfac, hcan⟩ := factor_closedImmersion p O K G i (fun n => (hi n).1)
  obtain ⟨q, hq⟩ := hfac G u (fun n => by rw [(hi n).2, hker n])
  have hiv : i ≫ v = 0 := by
    refine Hom.ext (funext fun n => BialgHom.ext fun b => ?_)
    have h := (kerIdeal_le_ker_iff (v.app n) (i.app n : G.A n →ₐ[O] K.A n)).1 (hi n).2.ge b
    change i.app n (v.app n b) = (1 : WithConv (G.A n →ₐc[O] K.A n)).ofConv b
    refine Eq.trans h ?_
    simp
  have hiu : i ≫ u = i := by
    have e := Preadditive.comp_add _ _ _ i u v
    rw [huv, hiv, add_zero, Category.comp_id] at e
    exact e.symm
  refine ⟨K, i, q, ?_, hq⟩
  apply hcan K
  rw [Category.assoc, hq, hiu, Category.id_comp]

end GlobalTheory.PDivGroup.IdemSplit

theorem GlobalTheory.PDivGroup.IdemSplit.idempotent_split_integers :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
      (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
      [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O →
      ∀ (G : PDivGroup p O) (u : G ⟶ G), u ≫ u = u →
        ∃ (H : PDivGroup p O) (i : H ⟶ G) (q : G ⟶ H), i ≫ q = 𝟙 H ∧ q ≫ i = u :=
  fun p _ _ _ _ _ _ O _ _ _ _ _ _ _ G u hu =>
    GlobalTheory.PDivGroup.IdemSplit.idempotent_split_of_isLocalRing p O G u hu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOnTangentEqDerivativeBoundingFunction
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.LieVal

open GlobalTheory.CatCoh

private theorem thickHomExt {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}}
    {pd : DividedPowers I} {s : X ⟶ Sp R} {T T' : Thick pd s} {f g : T ⟶ T'}
    (h : ∀ b, f.φ b = g.φ b) : f = g := by
  have hφ : f.φ = g.φ := AlgHom.ext h
  rcases f with ⟨φ, φ₀, comm, dp, pt⟩
  rcases g with ⟨ψ, ψ₀, comm', dp', pt'⟩
  obtain rfl : φ = ψ := hφ
  obtain rfl : φ₀ = ψ₀ := RingHom.ext fun c ↦ by
    obtain ⟨b, rfl⟩ := T.surj c
    rw [comm, comm']
  rfl

theorem main : ∀ {A : Over (Sp ℂ)} {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (r : Real K (A.hom ≫ 𝟙 _) (algebraMap ℂ (Hol F.V))) (k : K.K) (p : Tot I g), p ∈ K.W k → ∀ (w : Fin g → ℂ) (ρ : Hol (K.W k) →ₐ[ℂ] DualNumber ℂ), (∀ h, (ρ h).fst = h.fn p ∧ (ρ h).snd = fderiv ℂ h.fn p (0, w)) → ∀ (v : epsR ℂ ⟶ A), v.left = spMap ρ.toRingHom ≫ r.x k → ∀ (f : Form (A.hom ≫ 𝟙 _)) (per : Λ →+ Hol F.V) (q : GlobalTheory.CatCoh.C0 K.Oc), GlobalTheory.CatCoh.d0 K.Oc q = (r.coef.pullbackOneCocycle f.1).1 - (K.perZ per).1 → tanVal v f = fderiv ℂ (Hol.fn (W := K.W k) (q (K.triv k))) p (0, w) := by
  intro A I _ g Λ _ F K r k p hp w ρ hρ v hv f per q hq
  let e : Hol (K.W k) →+* DualNumber ℂ := (TrivSqZeroExt.inlHom ℂ ℂ).comp (Hol.ev p hp).toRingHom
  let T : K.Obj :=
    { k := k, C := DualNumber ℂ, alg := (e.comp (K.cst k)).toAlgebra
      J := RingHom.ker ((SqExt.dual ℂ).π : DualNumber ℂ →+* ℂ)
      nil := ⟨2, (SqExt.dual ℂ).sq⟩, ρ := e, ρ_cst := fun _ ↦ rfl }
  have hder : ∀ h : Hol (K.W k), fderiv ℂ h.fn p (0, w) = ∑ a, (dw a h).fn p * w a := fun h ↦ by
    have : ((0, w) : Tot I g) = ∑ a, w a • ((0, Pi.single a 1) : Tot I g) := by
      refine Prod.ext ?_ ?_
      · simp [Prod.fst_sum]
      · simp only [Prod.snd_sum, Prod.smul_snd]
        exact pi_eq_sum_univ' w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, map_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    exact congrArg (· * w a) (Hol.fn_der _ h hp).symm
  have hexp : ∀ h : Hol (K.W k), ρ h = e h + ∑ a, e (dw a h) * TrivSqZeroExt.inr (w a) := fun h ↦ by
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [(hρ h).1]
      simp [e, TrivSqZeroExt.fst_sum, Hol.ev_apply]
    · rw [(hρ h).2, hder]
      simp [e, TrivSqZeroExt.snd_sum, Hol.ev_apply, mul_comm]
  let a : K.triv k ⟶ T := Charts.ptHom T (K.le_refl k)
  let b : K.triv k ⟶ T := Charts.fromTriv T (K.le_refl k) ρ.toRingHom
    (fun c ↦ by
      change ρ (K.cst k c) = e (K.cst k c)
      rw [hexp]; simp [Charts.dw_cst])
    (Relation.ReflTransGen.single ⟨fun a ↦ TrivSqZeroExt.inr (w a), fun _ ↦ rfl,
      fun a b ↦ TrivSqZeroExt.inr_mul_inr _ _ _, fun h ↦ by
        simp only [RingHom.comp_apply, Charts.sh_refl]
        exact hexp h⟩)
  have ea := congrFun (congrFun (congrFun hq _) _) a
  have eb := congrFun (congrFun (congrFun hq _) _) b
  change ((show DualNumber ℂ from q T) - e (Charts.sh (K.le_refl k) (q (K.triv k))) : DualNumber ℂ) =
    (show DualNumber ℂ from ev f.1 (r.functor.map a)) - e (K.cst k (per 0)) at ea
  change ((show DualNumber ℂ from q T) - ρ (q (K.triv k)) : DualNumber ℂ) =
    (show DualNumber ℂ from ev f.1 (r.functor.map b)) - e (K.cst k (per 0)) at eb
  rw [Charts.sh_refl] at ea
  let E := SqExt.dual ℂ
  have hfst : (E.π : E.C →+* E.B).comp ρ.toRingHom = (Hol.ev p hp).toRingHom :=
    RingHom.ext fun h ↦ (hρ h).1.trans (Hol.ev_apply p hp h).symm
  have halg : ∀ c : ℂ, e (K.cst k (algebraMap ℂ (Hol F.V) c)) = algebraMap ℂ (DualNumber ℂ) c := fun c ↦ by
    have : K.cst k (algebraMap ℂ (Hol F.V) c) = algebraMap ℂ (Hol (K.W k)) c := rfl
    rw [this]
    change TrivSqZeroExt.inl (Hol.ev p hp (algebraMap ℂ _ c)) = _
    rw [AlgHom.commutes]; rfl
  let Φ : E.thick _ (E.red_w (pt_w v)) ⟶ r.obj T :=
    { φ := { RingHom.id (DualNumber ℂ) with commutes' := fun c ↦ (halg c).symm }
      φ₀ := (Ideal.Quotient.mk T.J).comp (TrivSqZeroExt.inlHom ℂ ℂ)
      comm := fun c ↦ Ideal.Quotient.eq.2 (by
        change (TrivSqZeroExt.inl (TrivSqZeroExt.fst (R := ℂ) (M := ℂ) c) - (show TrivSqZeroExt ℂ ℂ from c)).fst = 0
        rw [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inl, sub_self])
      dp := isDPMorphism_of_rat (C' := DualNumber ℂ) _ _ _ fun c hc ↦ hc
      pt := by
        have h0 : spMap ((Ideal.Quotient.mk T.J).comp (TrivSqZeroExt.inlHom ℂ ℂ)) ≫
            spMap (E.π : E.C →+* E.B) ≫ v.left = spMap ((Ideal.Quotient.mk T.J).comp e) ≫ r.x k := by
          rw [hv, ← Category.assoc (spMap (E.π : E.C →+* E.B)), ← Cris.spMap_comp, hfst, ← Category.assoc,
            ← Cris.spMap_comp]
        exact h0 }
  have mkHom : ∀ (C : Type) [CommRing C] [Algebra ℂ C] (ψ : Hol (K.W k) →ₐ[ℂ] C) (y : Sp C ⟶ A.left)
      (hy : y ≫ A.hom ≫ 𝟙 _ = spMap (algebraMap ℂ C)), y = spMap ψ.toRingHom ≫ r.x k →
      ∃ m : r.obj (K.triv k) ⟶ Thick.triv C y hy, ∀ c, m.φ c = ψ c := fun C _ _ ψ y hy e' ↦
    ⟨{ φ := { ψ.toRingHom with commutes' := fun c ↦ ψ.commutes c }
       φ₀ := Ideal.Quotient.lift ⊥ ψ.toRingHom fun c hc ↦ by rw [Ideal.mem_bot.1 hc, map_zero]
       comm := fun _ ↦ rfl
       dp := isDPMorphism_of_eq_bot _ rfl _ _
       pt := by
        refine Eq.trans ?_ e'.symm
        refine (Category.assoc _ _ _).symm.trans (congrArg (· ≫ r.x k) ?_)
        exact (Cris.spMap_comp _ _).symm }, fun _ ↦ rfl⟩
  obtain ⟨a', ha'⟩ := mkHom ℂ (Hol.ev p hp) _ (E.red_w (pt_w v)) (by
    rw [hv, ← Category.assoc, ← Cris.spMap_comp, hfst])
  obtain ⟨b', hb'⟩ := mkHom (DualNumber ℂ) ρ v.left (pt_w v) hv
  have e1 : r.functor.map a = a' ≫ E.secHom (E.red_w (pt_w v)) E.i E.π_i ≫ Φ := thickHomExt fun c ↦ by
    change e (Charts.sh (K.le_refl k) c) = TrivSqZeroExt.inl (a'.φ c)
    exact (congrArg e (Charts.sh_refl _ c)).trans (congrArg TrivSqZeroExt.inl (ha' c).symm)
  have e2 : r.functor.map b = b' ≫ E.idHom (pt_w v) ≫ Φ := thickHomExt fun c ↦ (hb' c).symm
  have z1 : ev f.1 a' = 0 := f.2 a' rfl rfl
  have z2 : ev f.1 b' = 0 := f.2 b' rfl rfl
  have g1 : ev f.1 (r.functor.map a) = Φ.φ (ev f.1 (E.secHom (E.red_w (pt_w v)) E.i E.π_i)) + ev f.1 Φ := by
    rw [e1]
    refine (ev_comp f.1 a' _).trans ?_
    rw [z1, map_zero, zero_add]
    exact ev_comp f.1 _ Φ
  have g2 : ev f.1 (r.functor.map b) = Φ.φ (ev f.1 (E.idHom (pt_w v))) + ev f.1 Φ := by
    rw [e2]
    refine (ev_comp f.1 b' _).trans ?_
    rw [z2, map_zero, zero_add]
    exact ev_comp f.1 _ Φ
  rw [g1] at ea
  rw [g2] at eb
  have key : (E.val v.left (pt_w v) f.1 : DualNumber ℂ) = ρ (q (K.triv k)) - e (q (K.triv k)) := by
    rw [SqExt.val_apply]
    have aux : ∀ x y z u s t c : DualNumber ℂ, x - y = s + u - c → x - z = t + u - c → s - t = z - y :=
      fun x y z u s t c h1 h2 ↦ by linear_combination h2 - h1
    exact aux _ _ _ _ _ _ _ ea eb
  rw [tanVal_apply, key, TrivSqZeroExt.snd_sub, (hρ _).2]
  exact sub_zero _

end GlobalTheory.AnPer.LieVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameWeightSingularWeightSmoothLeviNonneg
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.wt_psi_smooth_leviNonneg : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ δ : ℝ, (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), ∀ i y, y ∈ (A.chart i).source → y ∉ A.zeroSet s → ∀ ξ : Fin n → ℂ, 0 ≤ A.leviAt i (fun x => A.ph E i x + α * psi A L s x) y ξ) → ∀ (U : Set Y) (z : Y → V n) (β : ι → Y → ℂ), Etale A U z → A.IsFrameOn (A.kap + E) U β → (∀ y ∈ U, y ∉ A.zeroSet s) → SmoothR n (fun y : U => z y) (fun y : U => GlobalTheory.OTY.TwEst.wt A E β z y) ∧ SmoothR n (fun y : U => z y) (fun y : U => psi A L s y) ∧ ∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), LeviNonneg n (fun y : U => z y) (fun y : U => GlobalTheory.OTY.TwEst.wt A E β z y + α * psi A L s y) := by
  intro n Y _ _ _ _ _ ι La _ A E L s hs δ hlevi U z β hz hβ hU
  have hJ := _root_.GlobalTheory.OTY.jdet_isFrameOn_kap n Y ι La A U z hz
  have hW := _root_.GlobalTheory.frameWeight_levi n Y ι La A E U β (jdet A z) hz.isOpen hβ hJ
  have hP : ∀ x ∈ U, ∀ i, x ∈ (A.chart i).source →
      ContDiffAt ℝ ∞ (psi A L s ∘ (A.chart i).symm) (A.chart i x) :=
    fun x hx i hi => _root_.GlobalTheory.OTY.contDiffAt_psi_of_notMem_zeroSet n Y ι La A L s hs x (hU x hx) i hi
  have hS := (_root_.GlobalTheory.OTY.smooth_etale_of_smooth_in_charts n Y ι La A U z hz).2
  refine ⟨hS (GlobalTheory.OTY.TwEst.wt A E β z)
      (fun x hx => ⟨A.pick x, A.mem_pick x, (hW x hx _ (A.mem_pick x)).1⟩),
    hS (psi A L s) (fun x hx => ⟨A.pick x, A.mem_pick x, hP x hx _ (A.mem_pick x)⟩), ?_⟩
  intro α hα
  refine _root_.GlobalTheory.OTY.etale_leviNonneg n Y ι La A U z hz (fun y => GlobalTheory.OTY.TwEst.wt A E β z y + α * psi A L s y)
    (fun x hx => ⟨A.pick x, A.mem_pick x, ?_, fun ξ => ?_⟩)
  · exact (hW x hx _ (A.mem_pick x)).1.add (contDiffAt_const.mul (hP x hx _ (A.mem_pick x)))
  · have hc : ContDiffAt ℝ ∞ ((fun y => α * psi A L s y) ∘ (A.chart (A.pick x)).symm)
        (A.chart (A.pick x) x) :=
      contDiffAt_const.mul (hP x hx _ (A.mem_pick x))
    exact le_of_le_of_eq (hlevi α hα (A.pick x) x (A.mem_pick x) (hU x hx) ξ)
      ((hW x hx _ (A.mem_pick x)).2 _ hc ξ).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicPointExtOfIsSeparated
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.AnPer

theorem point_hol_ext_of_isSeparated : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E) {X : Scheme.{0}}, X.IsSeparated → ∀ x x' : Sp (Hol W) ⟶ X, (∀ (p : E) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = spMap (Hol.ev p hp).toRingHom ≫ x') → x = x' := by
  intro E _ _ W X hX x x' h
  have : IsSeparated (terminal.from X) := hX.isSeparated_terminal_from
  exact point_hol_ext E W X (⊤_ Scheme) (terminal.from X) x x' (terminal.hom_ext _ _) h

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCrystallineChernOnAnalyticThickenings
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem isChern_real : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (K : Charts F) (r : Real K s σ) (M : LB X) (j : K.K → M.ι), (∀ k, ⊤ ≤ r.x k ⁻¹ᵁ M.U (j k)) → ∀ z : SecondDeRham s, IsChern (dp0 B) s M z → ∃ (i : K.Obj → M.ι) (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C) (ℓ : GlobalTheory.CatCoh.Z2 K.Oc), (∀ T, ⊤ ≤ (r.obj T).x ⁻¹ᵁ M.U (i T)) ∧ (∀ (T T' : K.Obj) (φ : T ⟶ T') (hh : ⊤ ≤ (r.obj T').x ⁻¹ᵁ (M.U (i T') ⊓ M.U (i T))), Ideal.Quotient.mk T'.J (uu T T' φ) = evalAt (r.obj T').x (M.U (i T') ⊓ M.U (i T)) hh (M.g (i T') (i T)).val) ∧ (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), (show ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C from ℓ.1) T T' T'' φ ψ ∈ T''.J ∧ dpExp T''.δ ((show ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C from ℓ.1) T T' T'' φ ψ) * uu T T'' (φ ≫ ψ) = ψ.φ (uu T T' φ) * uu T' T'' ψ) ∧ r.coef.pull2 z = GlobalTheory.CatCoh.H2.mk K.Oc ℓ := by
  intro I _ g Λ _ F B _ X s σ K r M j hj z hz
  obtain ⟨i₀, hi₀, u₀, ℓ₀, h1, h2, h3⟩ := hz
  let G : K.Obj ⥤ (IsSmall (dp0 B) s M.U).FullSubcategory :=
    ObjectProperty.lift _ r.functor fun T ↦ ⟨j T.k, fun p _ ↦ hj T.k (Set.mem_univ _)⟩
  let n : GlobalTheory.CatCoh.CoefMap σ ((IsSmall (dp0 B) s M.U).ι ⋙ O (dp0 B) s) K.Oc :=
    { G := G
      α := fun T ↦ RingHom.id T.C
      naturality := fun _ _ ↦ rfl
      smul := fun T b c ↦ r.coef.smul T b c }
  refine ⟨fun T ↦ i₀ (G.obj T), fun T T' φ ↦ u₀ _ _ (G.map φ), n.pullbackTwoCocycle ℓ₀, fun T ↦ hi₀ (G.obj T),
    fun T T' φ _ ↦ h1 _ _ (G.map φ), fun T T' T'' φ ψ ↦ ?_, ?_⟩
  · have h := h2 _ _ _ (G.map φ) (G.map ψ)
    rw [← G.map_comp] at h
    exact h
  · rw [← n.pullCohomologyTwo_class, ← h3]
    obtain ⟨z, rfl⟩ := GlobalTheory.CatCoh.H2.mk_surjective _ z
    rfl

end GlobalTheory.AnPer
end

