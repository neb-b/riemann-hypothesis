module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfVeryAmpleBy

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialOfLocal
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalGlobalChar

open Filter Topology GlobalTheory.IdemSupport

section Adele

variable {F : Type} [Field F] [NumberField F]


open Classical in
def ind (S : Finset (HeightOneSpectrum (𝓞 F))) : Af F :=
  ⟨fun u => if u ∈ S then 1 else 0, Eventually.of_forall fun u => by
    by_cases h : u ∈ S
    · simp only [h, if_true]; exact one_mem _
    · simp only [h, if_false]; exact zero_mem _⟩

open Classical in
theorem ev_ind (S : Finset (HeightOneSpectrum (𝓞 F))) (u : HeightOneSpectrum (𝓞 F)) :
    evalV F u (ind S) = if u ∈ S then 1 else 0 := rfl

theorem fin_ext {a b : Af F} (h : ∀ u, evalV F u a = evalV F u b) : a = b := Subtype.ext (funext h)

theorem tendsto_ind_mul (α : Af F) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => ind S * α) atTop (𝓝 α) := by
  classical
  let T : Set (HeightOneSpectrum (𝓞 F)) := {u | α u ∈ (u.adicCompletionIntegers F : Set (u.adicCompletion F))}
  have hT : cofinite ≤ 𝓟 T := le_principal_iff.2 α.2
  let f : Finset (HeightOneSpectrum (𝓞 F)) → RestrictedProduct
      (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F)
      (fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F))) (𝓟 T) :=
    fun S => ⟨fun u => if u ∈ S then α u else 0, fun u hu => by
      by_cases h : u ∈ S
      · simp only [Set.mem_setOf_eq, h, if_true]; exact hu
      · simp only [Set.mem_setOf_eq, h, if_false]; exact zero_mem _⟩
  let a : RestrictedProduct
      (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F)
      (fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F))) (𝓟 T) := ⟨fun u => α u, fun u hu => hu⟩
  have hf : Tendsto f atTop (𝓝 a) := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro u
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ({u} : Finset _)] with S hS
    exact (if_pos (hS (Finset.mem_singleton_self u))).symm
  have h2 := ((RestrictedProduct.continuous_inclusion hT).tendsto a).comp hf
  refine Tendsto.congr (fun S => fin_ext fun u => ?_) h2
  rw [map_mul, ev_ind]
  change (if u ∈ S then α u else 0) = _
  split_ifs
  · exact (one_mul _).symm
  · exact (zero_mul _).symm

def eps (S : Finset (HeightOneSpectrum (𝓞 F))) : AF F := pairA F 1 (ind S)

theorem tendsto_eps_mul (a : AF F) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => eps S * a) atTop (𝓝 a) := by
  have := (tendsto_const_nhds (x := a.1)).prodMk_nhds (tendsto_ind_mul a.2)
  refine Tendsto.congr (f₁ := fun S => ((a.1, ind S * a.2) : Ainf F × Af F)) (fun S => ?_) this
  exact Prod.ext (one_mul _).symm rfl

theorem ind_mul_self (S : Finset (HeightOneSpectrum (𝓞 F))) : ind S * ind S = ind S :=
  fin_ext fun u => by rw [map_mul, ev_ind]; split_ifs <;> simp

theorem eps_mul_self (S : Finset (HeightOneSpectrum (𝓞 F))) : eps S * eps S = eps S :=
  Prod.ext (one_mul _) (ind_mul_self S)

theorem pl_mul_self (v : HeightOneSpectrum (𝓞 F)) :
    pairA F 0 (ind {v}) * pairA F 0 (ind {v}) = pairA F 0 (ind {v}) :=
  Prod.ext (mul_zero _) (ind_mul_self _)

theorem eps_cons (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    eps (S.cons v hv) * pairA F 0 (ind {v}) = pairA F 0 (ind {v}) ∧
    eps (S.cons v hv) * (1 - pairA F 0 (ind {v})) = eps S := by
  refine ⟨Prod.ext (mul_zero _) (fin_ext fun u => ?_), Prod.ext ?_ (fin_ext fun u => ?_)⟩
  · change evalV F u (ind (S.cons v hv) * ind {v}) = evalV F u (ind {v})
    rw [map_mul, ev_ind, ev_ind]
    by_cases h : u = v <;> simp [h]
  · change (1 : Ainf F) * (1 - 0) = 1
    simp
  · change evalV F u (ind (S.cons v hv) * (1 - ind {v})) = evalV F u (ind S)
    rw [map_mul, map_sub, map_one, ev_ind, ev_ind, ev_ind]
    by_cases h : u = v
    · subst h; simp [hv]
    · have hm : u ∈ S.cons v hv ↔ u ∈ S := by rw [Finset.mem_cons]; exact or_iff_right h
      by_cases h' : u ∈ S
      · rw [if_pos (hm.2 h'), if_pos h', if_neg (by simpa using h)]; simp
      · rw [if_neg (fun x => h' (hm.1 x)), if_neg h', zero_mul]

variable {E : Type} [Field E] [Algebra F E]

theorem tendsto_eps_tens (x : AF F ⊗[F] E) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => algebraMap (AF F) (AF F ⊗[F] E) (eps S) * x)
      atTop (𝓝 x) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  haveI : ContinuousSMul (AF F) (AF F ⊗[F] E) := IsModuleTopology.toContinuousSMul (AF F) _
  induction x using TensorProduct.induction_on with
  | zero => simpa only [mul_zero] using tendsto_const_nhds
  | tmul a e =>
    have h := (tendsto_eps_mul a).smul_const ((1 : AF F) ⊗ₜ[F] e)
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] at h
    refine h.congr fun S => ?_
    rw [← Algebra.smul_def, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => simpa only [mul_add] using hx.add hy

theorem tendsto_mix {n : ℕ} (M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => algebraMap (AF F) (AF F ⊗[F] E) (eps S) • M +
      (1 - algebraMap (AF F) (AF F ⊗[F] E) (eps S)) • (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) atTop (𝓝 M) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h := (tendsto_eps_tens ((M - 1) i j)).add_const ((1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) i j)
  rw [Matrix.sub_apply, sub_add_cancel] at h
  refine h.congr fun S => ?_
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end Adele

theorem tendsto_HA {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {ι : Type} {l : Filter ι}
    {p : ι → HA R σ J} {g : HA R σ J}
    (h1 : Tendsto (fun i => (HA.mat R σ J (p i)).1) l (𝓝 (HA.mat R σ J g).1))
    (h2 : Tendsto (fun i => (HA.mat R σ J (p i)⁻¹).1) l (𝓝 (HA.mat R σ J g⁻¹).1)) : Tendsto p l (𝓝 g) := by
  refine (IsEmbedding.subtypeVal.tendsto_nhds_iff).2 ?_
  refine (Units.isEmbedding_embedProduct.tendsto_nhds_iff).2 ?_
  exact h1.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp h2)

variable {D : D7}

theorem mem_GinfC (V : HSp D) {g : GA D V} (hg : SuppPl (eps ∅) V g) : g ∈ GinfC V := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have hf : finPart D (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (eps ∅)) = 0 := by
    have h0 : ind (∅ : Finset (HeightOneSpectrum (𝓞 D.host.F))) = 0 := fin_ext fun u => by
      rw [ev_ind, map_zero, if_neg (Finset.notMem_empty u)]
    change ind ∅ ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    rw [h0, TensorProduct.zero_tmul]
  have h := congrArg (finPart D) (hg i j)
  rw [map_mul, hf, zero_mul, Matrix.sub_apply, map_sub, eq_comm, sub_eq_zero] at h
  change finPart D (Formalism.L2.Theta.mt V g i j) = (1 : Matrix _ _ _) i j
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

theorem isPlaceIdem (v : HeightOneSpectrum (𝓞 D.host.F)) : IsPlaceIdem D v (pairA D.host.F 0 (ind {v})) :=
  ⟨ind {v}, rfl, by rw [ev_ind, if_pos (Finset.mem_singleton_self v)],
    fun w hw => by rw [ev_ind, if_neg (by simpa using hw)]⟩

theorem alg_idem {a : AF D.host.F} (h : a * a = a) :
    algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) a * algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) a =
      algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) a := by rw [← map_mul, h]

theorem triv_eps (V : HSp D) (ν : GA D V →* Circle) (hinf : ∀ g ∈ GinfC V, ν g = 1)
    (hpl : ∀ v g, SuppPl (pairA D.host.F 0 (ind {v})) V g → ν g = 1) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    ∀ g, SuppPl (eps S) V g → ν g = 1 := by
  induction S using Finset.cons_induction with
  | empty => exact fun g hg => hinf g (mem_GinfC V hg)
  | cons v S hv ih =>
    intro g hg
    obtain ⟨h1, h2⟩ := eps_cons S v hv
    have h1' := congrArg (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D)) h1
    have h2' := congrArg (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D)) h2
    rw [map_mul] at h1' h2'
    rw [map_sub, map_one] at h2'
    obtain ⟨g₁, g₂, s₁, s₂, e⟩ := exists_split V (alg_idem (pl_mul_self v)) (cA_algebraMap _) g
    have t₁ : g₁ ∈ suppGroup V (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (eps (S.cons v hv))) := fun i j => by
      rw [← s₁ i j, ← mul_assoc, h1']
    have t : g ∈ suppGroup V (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (eps (S.cons v hv))) := hg
    have t₂ : g₂ ∈ suppGroup V (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (eps (S.cons v hv))) := by
      have := mul_mem (inv_mem t₁) t
      rwa [e, inv_mul_cancel_left] at this
    have u₂ : SuppPl (eps S) V g₂ := fun i j => by
      rw [← h2', mul_assoc, s₂ i j, t₂ i j]
    rw [e, map_mul, hpl v g₁ s₁, ih g₂ u₂, mul_one]

theorem exists_approx (V : HSp D) (g : GA D V) :
    ∃ p : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D V, (∀ S, SuppPl (eps S) V (p S)) ∧ Tendsto p atTop (𝓝 g) := by
  choose p hp using fun S : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
    exists_piece V (alg_idem (eps_mul_self S)) (cA_algebraMap _) g
  choose q hq using fun S : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
    exists_piece V (alg_idem (eps_mul_self S)) (cA_algebraMap _) g⁻¹
  have hpq : ∀ S, (p S)⁻¹ = q S := fun S => by
    refine inv_eq_of_mul_eq_one_right (mt_inj V ?_)
    rw [mt_mul, hp, hq, mix_mul (alg_idem (eps_mul_self S)), ← mt_mul, mul_inv_cancel, mt_one, one_mul, mix_self]
  refine ⟨p, fun S => (suppF_iff V _ (p S)).2 (smul_mix (alg_idem (eps_mul_self S)) (hp S)), ?_⟩
  have a1 : Tendsto (fun S => Formalism.L2.Theta.mt V (p S)) atTop (𝓝 (Formalism.L2.Theta.mt V g)) :=
    (tendsto_mix _).congr fun S => (hp S).symm
  have a2 : Tendsto (fun S => Formalism.L2.Theta.mt V (p S)⁻¹) atTop (𝓝 (Formalism.L2.Theta.mt V g⁻¹)) :=
    (tendsto_mix _).congr fun S => by rw [hpq, hq]
  exact tendsto_HA _ _ _ a1 a2

theorem eq_one_of_local : ∀ (D : D7) (V : HSp D) (ν : GA D V →* Circle), Continuous ν → (∀ g ∈ GinfC V, ν g = 1) → (∀ e, IsSplitIdem D e → ∀ g, SuppAt e V g → ν g = 1) → (∀ v ε, NonSplitAt D v ε → ∀ g, SuppPl ε V g → ν g = 1) → ∀ g, ν g = 1 := by
  intro D V ν hν hinf hs hn g
  have hpl : ∀ v g, SuppPl (pairA D.host.F 0 (ind {v})) V g → ν g = 1 := fun v g hg => by
    by_cases h : ∃ e, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D)
        (pairA D.host.F 0 (ind {v}))
    · obtain ⟨e, he, h⟩ := h
      exact hs e he g fun i j => by rw [h]; exact hg i j
    · exact hn v _ ⟨isPlaceIdem v, h⟩ g hg
  obtain ⟨p, hp', hlim⟩ := exists_approx V g
  have hp : ∀ S, ν (p S) = 1 := fun S => triv_eps V ν hinf hpl S _ (hp' S)
  have h1 := (hν.tendsto g).comp hlim
  exact tendsto_nhds_unique h1 (tendsto_const_nhds.congr fun S => (hp S).symm)

end GlobalTheory.LocalGlobalChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingFormsIffProportionalPullbacks
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section
namespace GlobalTheory.HomFixUniv.MapIff

theorem eval₂_mul_of_isHomogeneous' {R S σ : Type} [CommRing R] [CommRing S] [Fintype σ] (g : R →+* S)
    (x : σ → S) (u : S) {F : MvPolynomial σ R} {d : ℕ} (hF : F.IsHomogeneous d) :
    MvPolynomial.eval₂ g (fun j => u * x j) F = u ^ d * MvPolynomial.eval₂ g x F := by
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = d := by
    have := hF (MvPolynomial.mem_support_iff.1 hm)
    rw [← this, Finsupp.weight_apply]
    simp [Finsupp.sum_fintype]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

section
variable {X Z : Scheme.{0}}

def gsH (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) : Γ(X, U) →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (r ⁻¹ᵁ U) z h).hom.comp (r.app U).hom

theorem gsH_apply (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    gsH r z U h a = gs r z U a := (gs_eq r z U h a).symm

theorem gs_eval₂Hom {R σ : Type} [CommRing R] (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U)
    (g : R →+* Γ(X, U)) (x : σ → Γ(X, U)) (F : MvPolynomial σ R) :
    gs r z U (MvPolynomial.eval₂Hom g x F) =
      MvPolynomial.eval₂Hom ((gsH r z U h).comp g) (fun j => gs r z U (x j)) F := by
  rw [← gsH_apply r z U h, ← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom]
  congr 2
  funext j
  exact gsH_apply r z U h _

theorem gs_cst_gc {R : Type} [CommRing R] (f : X ⟶ Sp R) (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (c : R) :
    gs r z U (GlobalTheory.AbLaw.cst f U c) = gc (r ≫ f) z c := by
  rw [GlobalTheory.MapToProj.gs_cst f r z U h c, gs_eq _ z ⊤ trivial]
  rfl

theorem gs_eval_cst {R σ : Type} [CommRing R] (f : X ⟶ Sp R) (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U)
    (x : σ → Γ(X, U)) (F : MvPolynomial σ R) :
    gs r z U (MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst f U) x F) =
      MvPolynomial.eval₂Hom (gc (r ≫ f) z) (fun j => gs r z U (x j)) F := by
  rw [gs_eval₂Hom r z U h, show (gsH r z U h).comp (GlobalTheory.AbLaw.cst f U) = gc (r ≫ f) z from
    RingHom.ext fun c => (gsH_apply r z U h _).trans (gs_cst_gc f r z U h c)]

end

variable {A₀ B₀ X T : Scheme.{0}} {N : LB A₀} {H : LB B₀} {mA mB : ℕ}

theorem exists_combSec (hN : N.IsLB) (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T)
    (c : Fin mA → Fin mB → Γ(T, ⊤)) : ∃ s : Fin mB → LB.Sec (N.pull φ), ∀ j z q, φ z ∈ N.U q →
      gs (𝟙 X) z ((N.pull φ).U (fun _ => q)) ((s j).f (fun _ => q)) = comb a φ p c z q j := by
  have le : ∀ J : PUnit → N.ι, (N.pull φ).U J ≤ φ ⁻¹ᵁ N.U (J PUnit.unit) := fun J _ hy => mem_pull.1 hy
  let F : Fin mB → ∀ J : PUnit → N.ι, Γ(X, (N.pull φ).U J) := fun j J =>
    ∑ i, (p.appLE ⊤ ((N.pull φ).U J) le_top).hom (c i j) *
      (φ.appLE (N.U (J PUnit.unit)) ((N.pull φ).U J) (le J)).hom ((a i).f (J PUnit.unit))
  have hF : ∀ j (J : PUnit → N.ι) z, z ∈ (N.pull φ).U J →
      gs (𝟙 X) z ((N.pull φ).U J) (F j J) = comb a φ p c z (J PUnit.unit) j := by
    intro j J z hz
    simp only [F, comb]
    rw [GlobalTheory.AmpleSpan.gs_sum' (𝟙 X) z _ hz]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gs_mul (𝟙 X) z _ hz]
    exact congrArg₂ (· * ·) ((gs_appLE p ⊤ _ _ (𝟙 X) z hz _).trans (by rw [Category.id_comp]))
      ((gs_appLE φ _ _ _ (𝟙 X) z hz _).trans (by rw [Category.id_comp]))
  refine ⟨fun j => ⟨F j, fun J J' => fn_ext fun y hy => ?_⟩, fun j z q hz => hF j _ z (mem_pull.2 hz)⟩
  have hJ : φ y ∈ N.U (J PUnit.unit) := mem_pull.1 hy.1
  have hJ' : φ y ∈ N.U (J' PUnit.unit) := mem_pull.1 hy.2
  rw [gs_res (𝟙 X) y _ hy, gs_mul (𝟙 X) y _ hy, gs_res (𝟙 X) y _ hy, gs_unit (𝟙 X) y _ hy,
    gm_pull_g N φ (𝟙 X) y J J' hy.1 hy.2, hF j J y hy.1, hF j J' y hy.2, Category.id_comp]
  simp only [comb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_compat (a i) φ y hJ hJ']
  ring

end GlobalTheory.HomFixUniv.MapIff

namespace GlobalTheory.HomFixUniv

open MapIff

theorem formsOK_iff_exists_proport : ∀ (Rg : Type) [CommRing Rg] (A₀ B₀ X T : Scheme.{0}) (f : A₀ ⟶ Sp Rg)
    (fB : B₀ ⟶ Sp Rg) (N : LB A₀) (H : LB B₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (b : Fin mB → LB.Sec H)
    (φ : X ⟶ A₀) (p : X ⟶ T) (t : T ⟶ Sp Rg) (c : Fin mA → Fin mB → Γ(T, ⊤)),
    GlobalTheory.AmpleSpan.EmbedsBy fB b → H.IsLB → N.IsLB → φ ≫ f = p ≫ t → GlobalTheory.HomFixUniv.Generates a φ p c →
    (GlobalTheory.HomFixUniv.FormsOK a fB b φ p t c ↔
      ∃ Ψ : X ⟶ B₀, Ψ ≫ fB = p ≫ t ∧ GlobalTheory.HomFixUniv.Proport a b φ p Ψ c) := by
  intro Rg _ A₀ B₀ X T f fB N H mA mB a b φ p t c hE hH hN _ hG
  constructor
  · intro hF
    cases mB with
    | zero =>
      have : IsEmpty X := ⟨fun z => by
        obtain ⟨q, hq⟩ := exists_chart hN (φ z)
        obtain ⟨j, -⟩ := hG z q hq
        exact j.elim0⟩
      exact ⟨isInitialOfIsEmpty.to B₀, isInitialOfIsEmpty.hom_ext _ _, fun z => (IsEmpty.false z).elim⟩
    | succ n =>
      obtain ⟨s, hs⟩ := exists_combSec (mB := n + 1) hN a φ p c
      have hva : GlobalTheory.AbLaw.VeryAmpleBy fB H b := (GlobalTheory.AmpleSpan.embedsBy_spec_iff fB b).1 hE
      have hcov : ⨆ j, nonzeroLocus (s j) = ⊤ := by
        refine eq_top_iff.2 fun z _ => ?_
        obtain ⟨q, hq⟩ := exists_chart hN (φ z)
        obtain ⟨j, hj⟩ := hG z q hq
        have hk : (𝟙 X : X ⟶ X) z ∈ (N.pull φ).U (fun _ => q) := mem_pull.2 hq
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, (GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs (s j) (𝟙 X) z hk).2
          (by rw [hs j z q hq]; exact hj)⟩
      have hforms : ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) Rg), F.IsHomogeneous d →
          (∀ k : H.ι, MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst fB (H.U k)) (fun j => (b j).f k) F = 0) →
          ∀ k : (N.pull φ).ι,
            MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst (p ≫ t) ((N.pull φ).U k)) (fun j => (s j).f k) F = 0 := by
        intro d F hFd hK k
        obtain ⟨q, rfl⟩ : ∃ q, k = fun _ => q := ⟨k PUnit.unit, rfl⟩
        refine fn_ext fun z hz => ?_
        have hq : φ z ∈ N.U q := mem_pull.1 hz
        have e : (fun j => gs (𝟙 X) z ((N.pull φ).U (fun _ => q)) ((s j).f (fun _ => q))) = comb a φ p c z q :=
          funext fun j => hs j z q hq
        rw [gs_eval_cst (p ≫ t) (𝟙 X) z _ hz, Category.id_comp, e, gs_eq (𝟙 X) z _ hz 0, map_zero, map_zero]
        exact hF d F hFd hK z q hq
      obtain ⟨Ψ, w, hΨ, -, hrel⟩ := GlobalTheory.exists_hom_of_veryAmpleBy Rg B₀ fB H n b hH hva X (p ≫ t) (N.pull φ) s
        (LB.isLB_linComb hN _ _) hcov hforms
      refine ⟨Ψ, hΨ, fun z q k hq hk j j' => ?_⟩
      have hz : z ∈ (N.pull φ).U (fun _ => q) := mem_pull.2 hq
      rw [hrel j z k (fun _ => q) hk hz, hrel j' z k (fun _ => q) hk hz, hs j z q hq, hs j' z q hq]
      ring
  · rintro ⟨Ψ, hΨ, hP⟩ d F hFd hK z q hq
    obtain ⟨j₀, hj₀⟩ := hG z q hq
    obtain ⟨j', hj'⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show Ψ z ∈ ⨆ j, nonzeroLocus (b j) by rw [hE.1]; trivial)
    obtain ⟨k, hk⟩ := GlobalTheory.AmpleSpan.exists_chart_of_mem (b j') hj'
    have hu' : IsUnit (gs Ψ z _ ((b j').f k)) := (GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs (b j') Ψ z hk).1 hj'
    have hPr := hP z q k hq hk
    have hB0 : IsUnit (gs Ψ z (H.U k) ((b j₀).f k)) := by
      have hu : IsUnit (gs Ψ z (H.U k) ((b j₀).f k) * comb a φ p c z q j') := hPr j' j₀ ▸ hu'.mul hj₀
      exact isUnit_of_mul_isUnit_left hu
    obtain ⟨u, hu⟩ := hj₀
    have hBC : ∀ j, gs Ψ z (H.U k) ((b j).f k) =
        (gs Ψ z (H.U k) ((b j₀).f k) * ↑u⁻¹) * comb a φ p c z q j := fun j => by
      have h1 := hPr j j₀
      rw [← hu] at h1
      calc gs Ψ z (H.U k) ((b j).f k) = gs Ψ z (H.U k) ((b j).f k) * ↑u * ↑u⁻¹ := by simp
        _ = gs Ψ z (H.U k) ((b j₀).f k) * comb a φ p c z q j * ↑u⁻¹ := by rw [h1]
        _ = _ := by ring
    have hK' := congrArg (gs Ψ z (H.U k)) (hK k)
    rw [gs_eval_cst fB Ψ z _ hk, hΨ, gs_eq Ψ z _ hk 0, map_zero, map_zero, funext hBC,
      MvPolynomial.coe_eval₂Hom, eval₂_mul_of_isHomogeneous' _ _ _ hFd] at hK'
    have hl : IsUnit ((gs Ψ z (H.U k) ((b j₀).f k) * ↑u⁻¹) ^ d) := (hB0.mul u⁻¹.isUnit).pow d
    rw [MvPolynomial.coe_eval₂Hom]
    exact hl.mul_right_eq_zero.1 hK'

end GlobalTheory.HomFixUniv
end
end

