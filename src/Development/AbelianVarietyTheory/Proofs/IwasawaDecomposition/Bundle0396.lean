module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedTopLevelChain
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0006
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFrameCharacterMulMovedPoint
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TopCh

theorem toGLm_entry {E : Type} [Field E] {n : ℕ} (f : Sp E n ≃ₗ[E] Sp E n) (i j : Fin n) :
    ((toGLm E n f : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j = f (Pi.single j 1) i := by
  simp [toGLm, Matrix.GeneralLinearGroup.toLin, LinearMap.GeneralLinearGroup.generalLinearEquiv]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
  {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem localComponent_eq_frame {hc : CMData F E} {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) (P : Q) :
    rhoP F P.1 g = Formalism.UG.bc (algebraMap E (P.1.adicCompletion E)) (toGLm E n (p.fr P)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show adAt F P.1 ((g : Matrix (Fin n) (Fin n) (AfE F E)) i j) = algebraMap E _ (((toGLm E n (p.fr P) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j)
  rw [h.fr P i j, toGLm_entry]

theorem rhoT_eq_iota {hc : CMData F E} {k t y x : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : GLG (E := E) (n := n) (SG := SG)) (θ : GLQ E n Q)
    (hk : ∀ P : Q, rhoP F P.1 k = 1) (h1 : IsPtOf hc (y * (k * t)) p)
    (h2 : IsPtOf hc (y * x * (k * t)) (((1, h, θ) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p)) (P : Q) :
    rhoT F P.1 t x = iotaP P.1 ((θ P)⁻¹) := by
  have e0 : rhoT F P.1 t x = (rhoP F P.1 (y * (k * t)))⁻¹ * rhoP F P.1 (y * x * (k * t)) := by
    rw [← map_inv, ← map_mul, show (y * (k * t))⁻¹ * (y * x * (k * t)) = t⁻¹ * (k⁻¹ * (x * k)) * t by group,
      map_mul, map_mul, map_mul, map_mul, map_inv (rhoP F P.1) k, hk P, inv_one, one_mul, mul_one]
    simp [rhoT]
  rw [e0, localComponent_eq_frame h1 P, localComponent_eq_frame h2 P]
  show _ * Formalism.UG.bc _ (toGLm E n ((1 : Sp E n ≃ₗ[E] Sp E n) * p.fr P * ((θ P)⁻¹).1)) = _
  rw [one_mul, map_mul, map_mul, inv_mul_cancel_left]
  rfl

theorem topChi_eq {K : Type} [Field K] (σ : K →+* ℂ) (U : Subgroup (GL (Fin n) (AfE F E))) (t : GL (Fin n) (AfE F E))
    (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ)
    (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ)))
    (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1)
    (x : topU U t Θ d) (θ : Θ.grp) (hx : ∀ P : Q, rhoT F P.1 t x.1 = iotaP P.1 ((θ.1 P)⁻¹)) :
    topChi σ U t Θ d hd N hdN hΘ x = Units.map (σ : K →* ℂ) (Θ.chr θ) := by
  have hθ : ∀ P : Q, θ.1 P ∈ (Θ P).H := fun P => θ.2 P (Set.mem_univ P)
  have key : ∀ P : Q, locChr P.1 (Θ P) (d P) (hd P) (hdN P) (hΘ P) ⟨rhoT F P.1 t x.1, rhoT_mem x.2 P⟩ =
      ((Θ P).lam ⟨θ.1 P, hθ P⟩)⁻¹ := by
    intro P
    have mem : iotaP P.1 ((θ.1 P)⁻¹) ∈ locLev P.1 (Θ P) (d P) := hx P ▸ rhoT_mem x.2 P
    have e : (⟨rhoT F P.1 t x.1, rhoT_mem x.2 P⟩ : locLev P.1 (Θ P) (d P)) = ⟨iotaP P.1 ((θ.1 P)⁻¹), mem⟩ := Subtype.ext (hx P)
    rw [e, ← map_inv]
    exact qbChr_rat (F := E) P.1 (algebraMap E (P.1.adicCompletion E)) (phi_int P.1) (phi_lt P.1) (Θ P) (d P) (hd P) (hdN P) (hΘ P)
      ((θ.1 P)⁻¹) (inv_mem (hθ P)) mem
  have ec : Θ.chr θ = ∏ P : Q, (Θ P).lam ⟨θ.1 P, hθ P⟩ := by
    unfold LevQFam.chr piChar
    exact MonoidHom.finsetProd_apply (M := ↥(Subgroup.pi Set.univ fun P : Q => (Θ P).H)) _ _ _
  unfold topChi
  rw [MonoidHom.inv_apply, MonoidHom.finsetProd_apply, ec, map_prod, ← _root_.inv_inj, inv_inv, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun P _ => ?_
  show Units.map (σ : K →* ℂ) (locChr P.1 (Θ P) (d P) (hd P) (hdN P) (hΘ P) ⟨rhoT F P.1 t x.1, rhoT_mem x.2 P⟩) = _
  rw [key, map_inv]

theorem chi_eq_of_J0 {K : Type} [Field K] [NeZero n] {hc : CMData F E} (Λ : LevFam E K n SG) (σ : K →+* ℂ)
    {U : Subgroup (GL (Fin n) (AfE F E))} (χ : U →* ℂˣ) {k t : GL (Fin n) (AfE F E)} (ht : t ∈ K1 hc n ST SG)
    (hχ : ∀ (x : U) (z : J0 hc n ST) (h : Λ.grp), z.1 = k⁻¹ * x.1 * k → redG hc n ST SG z = h.1⁻¹ →
      χ x = Units.map (σ : K →* ℂ) (Λ.chr h))
    (x : U) (h : Λ.grp) (hz : (k * t)⁻¹ * x.1 * (k * t) ∈ J0 hc n ST) (hr : redG hc n ST SG ⟨_, hz⟩ = h.1⁻¹) :
    χ x = Units.map (σ : K →* ℂ) (Λ.chr h) := by
  obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.1 ht
  refine hχ x (t' * ⟨_, hz⟩ * t'⁻¹) h ?_ ?_
  · show t'.1 * ((k * t'.1)⁻¹ * x.1 * (k * t'.1)) * t'.1⁻¹ = _
    group
  · rw [map_mul, map_mul, map_inv, MonoidHom.mem_ker.1 ht', hr, one_mul, inv_one, mul_one]

theorem chr_of_J0 {K : Type} [Field K] [NeZero n] (hc : CMData F E) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (d : Q → E)
    (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ)))
    (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1)
    (σ : K →+* ℂ) (U : Subgroup (GL (Fin n) (AfE F E))) (χ : U →* ℂˣ) (k t y : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q)
    (hk : ∀ P : Q, rhoP F P.1 k = 1) (ht : t ∈ K1 hc n ST SG)
    (hχ : ∀ (x : U) (z : J0 hc n ST) (h : Λ.grp), z.1 = k⁻¹ * x.1 * k → redG hc n ST SG z = h.1⁻¹ →
      χ x = Units.map (σ : K →* ℂ) (Λ.chr h))
    (x : topU U t Θ d) (h : Λ.grp) (θ : Θ.grp) (h1 : IsPtOf hc (y * (k * t)) p)
    (h2 : IsPtOf hc (y * x.1 * (k * t)) (((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p))
    (hz : (k * t)⁻¹ * x.1 * (k * t) ∈ J0 hc n ST) (hr : redG hc n ST SG ⟨_, hz⟩ = h.1⁻¹) :
    χ ⟨x.1, topU_le _ _ _ _ x.2⟩ * topChi σ U t Θ d hd N hdN hΘ x = Units.map (σ : K →* ℂ) (Λ.chr h * Θ.chr θ) := by
  rw [chi_eq_of_J0 Λ σ χ ht hχ ⟨x.1, topU_le _ _ _ _ x.2⟩ h hz hr,
    topChi_eq σ U t Θ d hd N hdN hΘ x θ fun P => rhoT_eq_iota h.1 θ.1 hk h1 h2 P, map_mul]

theorem chi_mul_topChi_moved : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1) (σ : K →+* ℂ) (U : Subgroup (GL (Fin n) (AfE F E))) (χ : U →* ℂˣ) (k t y : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), k ∈ UAd hc n → (∀ P : Q, rhoP F P.1 k = 1) → t ∈ K1 hc n ST SG → (∀ (x : U) (z : J0 hc n ST) (h : Λ.grp), z.1 = k⁻¹ * x.1 * k → redG hc n ST SG z = h.1⁻¹ → χ x = Units.map (σ : K →* ℂ) (Λ.chr h)) → ∀ (x : topU U t Θ d) (h : Λ.grp) (θ : Θ.grp), IsPtOf hc (y * (k * t)) p → IsPtOf hc (y * x.1 * (k * t)) (((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) → χ ⟨x.1, topU_le _ _ _ _ x.2⟩ * topChi σ U t Θ d hd N hdN hΘ x = Units.map (σ : K →* ℂ) (Λ.chr h * Θ.chr θ) := by
  intro F E K _ _ _ _ _ _ _ hc n _ ST SG Q Λ Θ d hd N hdN hΘ σ U χ k t y p _ hk ht hχ x h θ h1 h2
  have e : y * (k * t) * ((k * t)⁻¹ * x.1 * (k * t)) = y * x.1 * (k * t) := by group
  obtain ⟨hz, hr⟩ := ((isPtOf_mul_J0 F E hc n ST SG Q (y * (k * t)) ((k * t)⁻¹ * x.1 * (k * t)) p
    (((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) h.1).1 h1 (e ▸ h2)).2 rfl
  exact chr_of_J0 hc Λ Θ d hd N hdN hΘ σ U χ k t y p hk ht hχ x h θ h1 h2 hz hr

end GlobalTheory.Mem.Col2.TopCh

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatrixModPlaceBasisChangeEqConj
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymFrame

theorem val_mul_nsmul {Q ι : Type} [AddCommGroup Q] [Fintype ι] {g : ℕ} [NeZero g] (β : Q) (hβ : g • β = 0)
    (x y : ι → ZMod g) : (∑ i, x i * y i).val • β = ∑ i, (x i).val • (y i).val • β := by
  have h1 : (∑ i, x i * y i) = ((∑ i, (x i).val * (y i).val : ℕ) : ZMod g) := by
    push_cast
    simp
  rw [h1, ZMod.val_natCast]
  have h2 : ∀ n : ℕ, (n % g) • β = n • β := fun n => by
    conv_rhs => rw [← Nat.mod_add_div n g, add_nsmul, mul_comm, mul_nsmul', hβ, nsmul_zero, add_zero]
  rw [h2, ← Finset.sum_nsmul_assoc]
  simp [mul_smul]

theorem basisChange_quot {Q ι : Type} [AddCommGroup Q] [Fintype ι] [DecidableEq ι] {g : ℕ} [NeZero g] (f : Q →+ Q)
    (β υ : ι → Q) (hβ : ∀ i, g • β i = 0) (M P N : Matrix ι ι (ZMod g)) (hPN : P * N = M * P)
    (hυ : ∀ j, υ j = ∑ i, (P i j).val • β i) (hf : ∀ i, f (β i) = ∑ j, (M j i).val • β j) (j : ι) :
    f (υ j) = ∑ m, (N m j).val • υ m := by
  have e1 : f (υ j) = ∑ l, ((M * P) l j).val • β l := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hυ, map_sum]
    simp only [map_nsmul, hf, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_apply, val_mul_nsmul _ (hβ l)]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  rw [e1, ← hPN]
  simp only [hυ, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_apply, val_mul_nsmul _ (hβ l)]
  exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

theorem basisChange_mod {V ι : Type} [AddCommGroup V] [Fintype ι] [DecidableEq ι] {g : ℕ} [NeZero g]
    (W : AddSubgroup V) (f : V →+ V) (hW : ∀ v ∈ W, f v ∈ W)
    (β υ : ι → V) (hβ : ∀ i, g • β i ∈ W) (M P N : Matrix ι ι (ZMod g)) (hPN : P * N = M * P)
    (hυ : ∀ j, υ j - ∑ i, (P i j).val • β i ∈ W) (hf : ∀ i, f (β i) - ∑ j, (M j i).val • β j ∈ W) (j : ι) :
    f (υ j) - ∑ m, (N m j).val • υ m ∈ W := by
  have key : ∀ a b : V, a - b ∈ W ↔ QuotientAddGroup.mk' W a = QuotientAddGroup.mk' W b := fun a b => by
    rw [← sub_eq_zero, ← map_sub, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  have h := basisChange_quot (QuotientAddGroup.map W W f (fun v hv => hW v hv))
    (fun i => QuotientAddGroup.mk' W (β i)) (fun i => QuotientAddGroup.mk' W (υ i))
    (fun i => by rw [← map_nsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]; exact hβ i)
    M P N hPN
    (fun j => by
      have := (key _ _).1 (hυ j)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [this, map_sum]; simp only [map_nsmul])
    (fun i => by
      have := (key _ _).1 (hf i)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at this
      simp only [map_nsmul] at this
      rw [← this]; rfl) j
  set_option synthInstance.maxHeartbeats 100000 in
    rw [key, map_sum]
  simp only [map_nsmul]
  rw [← h]; rfl

variable {D : D7} (X : HidaSetting D)

theorem inclE_smul_mem_wLf (w : HeightOneSpectrum (𝓞 D.host.E)) (a : 𝓞 X.B.I.E)
    (ha : ∃ b ∈ w.asIdeal, X.ιE (a : X.B.I.E) = (b : D.host.E)) {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) :
    Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a : X.B.I.E) • y ∈ wLf X w := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨l, hl⟩, rfl⟩ := hz
    have hm : (a : X.B.I.E) • l ∈ wLat X w := Submodule.subset_span ⟨a, ha, l, hl, rfl⟩
    have e : Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a : X.B.I.E) •
        (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (l i)) =
        fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (((a : X.B.I.E) • l) i) := by
      funext i
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]
    rw [e]
    exact Submodule.subset_span ⟨⟨_, hm⟩, rfl⟩
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ c ha

theorem fmat_mulVec_mem_wLf (w : HeightOneSpectrum (𝓞 D.host.E)) {k : X.B.I.Gf} (hk : k ∈ X.B.I.Kset)
    {y : VA X.B.I} (hy : y ∈ wLf X w) : X.B.I.fmat k *ᵥ y ∈ wLf X w := by
  have hz : ∀ z ∈ wLat X w, ∀ c : 𝓞 X.B.I.E, X.B.I.fmat k *ᵥ incl X.B.I (c • z) ∈ wLf X w := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, l, hl, rfl⟩ := hz
      intro c
      have e : incl X.B.I (c • (a : X.B.I.E) • l) =
          Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a : X.B.I.E) • incl X.B.I (c • l) := by
        rw [smul_comm]
        funext i
        exact map_mul (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) (a : X.B.I.E) ((c • l) i)
      rw [e, Matrix.mulVec_smul]
      refine inclE_smul_mem_wLf X w a ha ((hk _).1 ?_)
      exact Submodule.subset_span ⟨⟨_, X.B.I.L.smul_mem c hl⟩, rfl⟩
    | zero =>
      intro c
      have e : incl X.B.I (c • (0 : Fin X.B.I.n → X.B.I.E)) = 0 := by
        rw [smul_zero]; funext i; simp [incl]
      rw [e, Matrix.mulVec_zero]; exact zero_mem _
    | add a b _ _ ha hb =>
      intro c
      have e : incl X.B.I (c • (a + b)) = incl X.B.I (c • a) + incl X.B.I (c • b) := by
        rw [smul_add]; funext i; simp only [incl, Pi.add_apply, map_add (f := _)]
      rw [e, Matrix.mulVec_add]; exact add_mem (ha c) (hb c)
    | smul d a _ ha =>
      intro c
      rw [smul_smul]; exact ha _
  induction hy using Submodule.span_induction with
  | mem z h =>
    obtain ⟨⟨l, hl⟩, rfl⟩ := h
    have := hz l hl 1
    rw [one_smul] at this
    exact this
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul c a _ ha =>
    have e : X.B.I.fmat k *ᵥ (c • a) = c • (X.B.I.fmat k *ᵥ a) :=
      Matrix.mulVec_smul _ (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) a
    rw [e]; exact Submodule.smul_mem _ c ha

theorem isMatIn_basisChange : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd) (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E), FixRed X red b → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (P : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) (u : Fin D.R.r → VA X.B.I), (∀ j, u j - ∑ i, ((((((P : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) i j).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • incl X.B.I (b kv i) ∈ wLf X (D.naut.plGw kv.1 kv.2)) → ∀ k ∈ X.B.I.Kset, GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) u k ((((P⁻¹ * red k kv * P) : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) := by
  intro D X red b hf kv hg P u hu k hk j
  haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
  have h := basisChange_mod (g := D.host.g kv.1) (wLf X (D.naut.plGw kv.1 kv.2)).toAddSubgroup
    (Matrix.mulVecLin (X.B.I.fmat k)).toAddMonoidHom
    (fun v hv => fmat_mulVec_mem_wLf X _ hk hv)
    (fun i => incl X.B.I (b kv i)) u
    (fun i => by
      have h1 := inclE_smul_mem_wLf X (D.naut.plGw kv.1 kv.2) ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E)
        ⟨_, hg, by simp⟩ (y := incl X.B.I (b kv i)) (Submodule.subset_span ⟨⟨_, (hf kv).1.1 i⟩, rfl⟩)
      have e : Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E) : X.B.I.E) =
          ((D.host.g kv.1 : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) := by
        simp [map_natCast]
      rw [e, Nat.cast_smul_eq_nsmul] at h1
      exact h1)
    ((red k kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix _ _ _) (P : Matrix _ _ _)
    (((P⁻¹ * red k kv * P) : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix _ _ _)
    (by rw [← Units.val_mul, ← Units.val_mul]; congr 1; group)
    (fun j => by
      have := hu j
      simp only [Nat.cast_smul_eq_nsmul] at this
      exact this)
    (fun i => by
      have := (hf kv).2 k hk i
      simp only [Nat.cast_smul_eq_nsmul] at this
      exact this) j
  simp only [Nat.cast_smul_eq_nsmul]
  exact h

end GlobalTheory.Mem.SymFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemGlintOfEntries
section
namespace GlobalTheory.MemGlintOfEntries

theorem mem_glint_of_entries {K : Type} [inst : Field K] {n : ℕ} (O : Subring K)
    (g : GL (Fin n) K)
    (h : ∀ (i j : Fin n), (↑g : Matrix (Fin n) (Fin n) K) i j ∈ O)
    (h' : ∀ (i j : Fin n), (↑g⁻¹ : Matrix (Fin n) (Fin n) K) i j ∈ O) :
    g ∈ Formalism.UG.GLint (Fin n) O := by
  let A : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨_, h i j⟩
  let B : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨_, h' i j⟩
  have hA : O.subtype.mapMatrix A = (↑g : Matrix (Fin n) (Fin n) K) := by
    ext i j; rfl
  have hB : O.subtype.mapMatrix B = (↑g⁻¹ : Matrix (Fin n) (Fin n) K) := by
    ext i j; rfl
  have hinj : Function.Injective
      (O.subtype.mapMatrix : Matrix (Fin n) (Fin n) O → Matrix (Fin n) (Fin n) K) := by
    intro X Y hXY
    ext i j
    exact congrFun (congrFun hXY i) j
  have hAB : A * B = 1 := by
    apply hinj
    rw [map_mul, map_one, hA, hB]
    exact Units.mul_inv g
  have hBA : B * A = 1 := by
    apply hinj
    rw [map_mul, map_one, hA, hB]
    exact Units.inv_mul g
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  apply Units.ext
  ext i j
  rfl

end GlobalTheory.MemGlintOfEntries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemIffRead
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TypeRead

section Read

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {u : B.Word} {j : ℕ} {Ch : Type} {chOf : (I.stp u I.mu0 j).Cl → Ch}
  {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N j) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N j))} {chi : ∀ β, U β →* ℂˣ}
  {y : (I.stp u I.mu0 j).Cl → GA B (B.R.N j)} {st : ∀ c, (I.stp u I.mu0 j).Stab c → GL (Fin (B.R.N j)) B.host.E}
  {k : Ch → GA B (B.R.N j)}


set_option maxHeartbeats 2000000 in
theorem mem_iff_read (H : I.Reads u I.mu0 j chOf Lb U chi y st k) (c : (I.stp u I.mu0 j).Cl) (x : GA B (B.R.N j))
    (hx : x ∈ UAd B.sp.cm (B.R.N j)) :
    x ∈ U (chOf c) ↔ ∃ (hJ : x ∈ J0 B.sp.cm (B.R.N j) ((B.primes X).vT u))
      (hm : (redG B.sp.cm (B.R.N j) ((B.primes X).vT u) (B.primes X).vGs ⟨x, hJ⟩)⁻¹ ∈
        (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) j c.1).grp),
      cosetIn ((I.stp u I.mu0 j).act c.1 (1, ⟨_, hm⟩, 1) ((I.stp u I.mu0 j).rep c)) = cosetIn ((I.stp u I.mu0 j).rep c) := by
  constructor
  · intro hxU
    obtain ⟨q, hq⟩ := OneLevel.pt_exists I.twistPrimes_reference_tuple_eq_empty (OneLevel.reads_base H (chOf c)) (OneLevel.reads_pt H c) hx
    obtain ⟨κ, h1, h2, h3⟩ := (H.lev c x q hq).1 hxU
    subst h2
    obtain ⟨γ, h, θ⟩ := κ
    obtain rfl : γ = 1 := Subtype.ext ((toGLm B.fields.E (B.R.N j)).injective (h1.trans (map_one _).symm))
    obtain ⟨hJ, hr⟩ := OneLevel.pt_read I.twistPrimes_reference_tuple_eq_empty (OneLevel.reads_base H (chOf c)) (OneLevel.reads_pt H c) h.1 θ.1 hq
    obtain rfl : θ = 1 := Subtype.ext (funext fun P => (Finset.eq_empty_iff_forall_notMem.1 I.twistPrimes_reference_tuple_eq_empty P.1 P.2).elim)
    refine ⟨hJ, hr ▸ h.2, ?_⟩
    have e : (⟨_, hr ▸ h.2⟩ : (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) j c.1).grp) = h := Subtype.ext hr
    rw [e]
    exact h3
  · rintro ⟨hJ, hm, hc⟩
    exact OneLevel.mem_of_read H c x hJ hm hc

end Read

end GlobalTheory.Mem.Col2.TypeRead

namespace GlobalTheory.Mem.Col2.TypeRead

section Put

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E))

theorem put_mem_J0 (v : HeightOneSpectrum (𝓞 F)) (hT : v ∉ plUnder F ST) (x : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hx : x ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST)) : rll_put n v x ∈ J0 hc n ST := by
  have hxU : x ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) := hx.1
  have hxS : x ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n)) := by
    rw [← rll_locL_base n ST v hT]; exact hx.2
  have hS := rll_put_mem_St n v hxS
  refine (mem_mirabolicLevel_iff_reduction hc n ST).2 ⟨rll_put_mem_UAd hc n v hxU, hS, fun P hP => ?_⟩
  rw [rll_put_red n v x hS P (fun h => hT ⟨P, hP, h⟩)]
  exact Subgroup.one_mem _

theorem red_put_off (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hJ : rll_put n v x ∈ J0 hc n ST)
    (w : SG) (hw : ¬ IsOver v w.1) : redG hc n ST SG ⟨rll_put n v x, hJ⟩ w = 1 :=
  rll_put_red n v x (congruence_subgroup_le_stabilizer hc n ST hJ) w.1 hw

theorem red_put_at {gp : Fin 2 → ℕ} (G : GLoc F E hc.sig gp) (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp a : 𝓞 F) ∈ v.asIdeal)
    (w : SG) (e : (𝓞 E ⧸ w.1.asIdeal) ≃+* kv F v)
    (hcomp : ∀ z : Formalism.L2.Herm.intAf F E, ∃ hz : G.phi a v h (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e (resS F w.1 z))
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hJ : rll_put n v x ∈ J0 hc n ST) :
    ((redG hc n ST SG ⟨rll_put n v x, hJ⟩ w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).map e =
      redM F v (G.mat a v h 1 x) := by
  have hcomp' : ∀ (z : Formalism.L2.Herm.intAf F E), ∃ hz : gloPhi v (G.sp a v h) (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e (resS F w.1 z) := hcomp
  have hw := GlobalTheory.Mem.LevStd.gloRho_zero_of_compat v (G.sp a v h) (G.sp_alg a v h) w.1 e hcomp'
  have hgE := GlobalTheory.Mem.LevStd.gloE_eq_of_compat v (G.sp a v h) (G.sp_alg a v h) w.1 e hcomp'
  have h1 := gco_red_map n v (G.sp a v h) (G.sp_alg a v h) w.1 hw (congruence_subgroup_le_stabilizer hc n ST hJ)
  have hG : G.mat a v h 1 x = ((bc (gloPhi v (G.sp a v h)) (bc (prV (E := E) v) (rll_put n v x)) : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
    rw [rll_put_self]; simp only [GLoc.mat, inv_one, one_mul, mul_one]; rfl
  rw [hG, ← h1]
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply, hgE]
  rfl

end Put

end GlobalTheory.Mem.Col2.TypeRead

namespace GlobalTheory.Mem.Col2.TypeRead

section Coset

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}

def cvec (p : PtAt R sel mu cst u j) (P : rowSG Pr sel mu) : Fin (R.N j) → 𝓞 X.E ⧸ P.1.asIdeal :=
  redV P.1 ((qOf P.1 : X.E) • Classical.epsilon fun z => z ∈ cosetIn p P)

end Coset

end GlobalTheory.Mem.Col2.TypeRead

namespace GlobalTheory.Mem.Col2.TypeRead

section Fix

variable {K L : Type} [CommRing K] [CommRing L] {n : ℕ}

theorem fix_inv_iff (M : GL (Fin n) K) (c : Fin n → K) :
    ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ c = c ↔ (M : Matrix (Fin n) (Fin n) K) *ᵥ c = c := by
  constructor
  · intro h
    conv_lhs => rw [← h]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  · intro h
    conv_lhs => rw [← h]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem fix_map_iff (e : K ≃+* L) (M : Matrix (Fin n) (Fin n) K) (c : Fin n → K) :
    M.map e *ᵥ (fun i => e (c i)) = (fun i => e (c i)) ↔ M *ᵥ c = c := by
  have h : M.map e *ᵥ (fun i => e (c i)) = fun i => e ((M *ᵥ c) i) := by
    have := RingHom.map_mulVec (e : K →+* L) M c
    funext i
    exact (this i).symm
  rw [h]
  constructor
  · intro h'
    funext i
    exact e.injective (congrFun h' i)
  · intro h'
    rw [h']

end Fix

end GlobalTheory.Mem.Col2.TypeRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SecondGOfHalves
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.GroupRetwisting

theorem secondG_congr {α : Type*} (g : ∀ P : Pre, Fr P → α) {P P' : Pre} {f : Fr P} {f' : Fr P'} (h : P = P') (hf : HEq f f') :
    g P f = g P' f' := by
  subst h
  rw [eq_of_heq hf]

end GlobalTheory.Mem.Top.GroupRetwisting
end

