module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Formalism.LocalToGlobal.HermitianForms.Bundle0005
public import Formalism.LocalToGlobal.Columns.RecLevelTop
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0042

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
section
noncomputable section

namespace GlobalTheory.SplitRead

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh GlobalTheory.RowTie GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsBlockVec {r t : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (χ : kˣ →* ℂˣ)
    (π : Representation ℂ (GL (Fin (r + t)) k) W) (v : W) : Prop :=
  ∀ h ∈ KO k (Fin (r + t)),
    (∀ (i : Fin t) (j : Fin r), valuation k (h.val (Fin.natAdd r i) (Fin.castAdd t j)) < 1) →
    (∀ i j : Fin r, valuation k (h.val (Fin.castAdd t i) (Fin.castAdd t j) - if i = j then 1 else 0) < 1) →
    ∀ u : kˣ, (u : k) = (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det → π h v = (χ u : ℂ) • v


variable (k) in
def BlockSplit : Prop := ∀ (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (v : π.V), IsSmoothChar χ → IsTame χ →
  v ≠ 0 → IsBlockVec χ π.π v →
  (∃ (π₁ : Irr k r) (π₂ : Irr k t), IsSpherical π₂.π ∧
    Nonempty (π.π.Equiv (prod₂ π₁.π (twist π₂.π (detChar (Fin t) χ))))) ∨
  ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsCuspSupport π.π d (fun a => (σ a).π) ∧
    t < Set.ncard {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (detRep (Fin (d a)) (χ * unrChar k α)))}

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def RecSupp (rc : ∀ n, Irr k n → WD h) : Prop :=
  ∀ (n s : ℕ) (π : Irr k n) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsCuspSupport π.π d (fun a => (σ a).π) →
    ∀ g : Weil h, (rc n π).charPol g = ∏ a, (rc (d a) (σ a)).charPol g

def RecUnit (rc : ∀ n, Irr k n → WD h) : Prop :=
  ∀ (χ : kˣ →* ℂˣ) (c : Irr k 1), IsUnitaryChar χ → Nonempty (c.π.Equiv (detRep (Fin 1) χ)) →
    ∀ g : Weil h, ∀ α ∈ (rc 1 c).eig g, ‖α‖ = 1

end Local

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
  {T : WDTie N A} (S : Reading T)

def SuppLaws : Prop := ∀ i w hw, RecSupp (S i w hw).rc

def TypeBlock (i : N.Loc) (w : PlE H) (hw : IsSplitPl H w) : Prop :=
  IsTame (S i w hw).mu ∧ ∀ P, ∃ v, v ≠ 0 ∧ IsBlockVec (S i w hw).mu ((S i w hw).rep P).π v

def BlockSplitAll (E : Type) [Field E] [NumberField E] : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), BlockSplit (w.adicCompletion E)

variable (N A)

def MuInt : Prop := ∀ (i : N.Loc) (τ : H.E →+* ℂ), ∀ z ∈ A.infG (A.muC i) τ, ∃ m : ℤ, z = (m : ℂ)

def ChiIne : Prop := ∀ (i : N.Loc) (w : PlE H), w ∉ placesOver H.E (N.l i) →
  ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol (A.locG (A.muC i) w) σ = X - C (iotaO N A i (chi1 N i σ))

def XiOverO : Prop := ∀ i : N.Loc, ∃ ξ : G H.E N.Om →* (N.O i)ˣ, Continuous (fun g => ((ξ g : (N.O i)ˣ) : N.O i)) ∧
  ∀ w : PlE H, w ∉ placesOver H.E (N.l i) → (∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), ξ σ = 1) ∧
    ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om), IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
      A.frobEig (A.lpTw (A.locG A.etaTinv w) (-(R.t : ℝ) / 2)) = {iotaO N A i ((ξ σ : (N.O i)ˣ) : N.O i)}

def RowPoint : Prop := ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ →
  ∃ i' : N.Loc, N.j i' = N.j i ∧ N.l i' = N.l i ∧ (∀ w, IsSplitPl H w → A.locW i' σ w = A.locW i σ w) ∧
    (∃ φ : N.O i' ≃+* N.O i, Continuous φ ∧ ∀ z, iotaO N A i (φ z) = iotaO N A i' z) ∧
    ∃ (P : A.AV i') (x : N.X i'), thetaOf N A i' σ P ∧ A.ptV i' P = some x

end GlobalTheory.SplitRead
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FracZeroOfPos
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {d : ℕ}

def pw (f : Fin d → R) : Submonoid R := Submonoid.powers (∏ j, f j)

def omitted (f : Fin d → R) (M : Type) [AddCommGroup M] [Module R M] : Submodule R (LocalizedModule (pw f) M) :=
  Submodule.span R {z | ∃ (j : Fin d) (k : ℕ) (m : M), z = LocalizedModule.mk (f j ^ k • m) ⟨(∏ l, f l) ^ k, by exact ⟨k, rfl⟩⟩}

abbrev LC (f : Fin d → R) (M : Type) [AddCommGroup M] [Module R M] : Type :=
  LocalizedModule (pw f) M ⧸ omitted f M

def frac (f : Fin d → R) {M : Type} [AddCommGroup M] [Module R M] (m : M) (k : ℕ) : LC f M :=
  Submodule.Quotient.mk (LocalizedModule.mk m ⟨(∏ l, f l) ^ k, by exact ⟨k, rfl⟩⟩)

theorem frac_prod_smul (f : Fin d → R) (m : M) (k : ℕ) : frac f ((∏ l, f l) • m) (k + 1) = frac f m k := by
  unfold frac
  congr 1
  rw [LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, smul_smul, pow_succ]

theorem frac_zero_of_pos (f : Fin d → R) (hd : 0 < d) (m : M) : frac f m 0 = 0 := by
  unfold frac
  rw [Submodule.Quotient.mk_eq_zero]
  apply Submodule.subset_span
  exact ⟨⟨0, hd⟩, 0, m, by simp⟩

def IsRes {B : Type} [CommRing B] [Algebra ℂ B] (s : Fin d → B) (e : B →ₐ[ℂ] MvPowerSeries (Fin d) ℂ)
    (ρ : LC s (Om ℂ B d) →ₗ[ℂ] ℂ) : Prop :=
  (∀ j, e (s j) = MvPowerSeries.X j) ∧
  (∀ ω : Om ℂ B d, ∃ h : B, ω = h • exteriorPower.ιMulti B d fun j => D ℂ B (s j)) ∧
  ∀ (k : ℕ) (h : B), ρ (frac s (h • exteriorPower.ιMulti B d fun j => D ℂ B (s j)) (k + 1)) =
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm fun _ => k) (e h)

namespace IsRes

variable {B : Type} [CommRing B] [Algebra ℂ B] {s : Fin d → B} {e : B →ₐ[ℂ] MvPowerSeries (Fin d) ℂ}
  {ρ : LC s (Om ℂ B d) →ₗ[ℂ] ℂ}

end IsRes

end GlobalTheory.W1

namespace GlobalTheory.W1.Ex

def rho0 (s : Fin 0 → ℂ) : LC s (Om ℂ ℂ 0) →ₗ[ℂ] ℂ :=
  (Submodule.liftQ (omitted s (Om ℂ ℂ 0))
    ((exteriorPower.zeroEquiv ℂ Ω[ℂ⁄ℂ]).toLinearMap ∘ₗ
      LocalizedModule.lift (pw s) LinearMap.id (fun u => by
        obtain ⟨n, hn⟩ := u.2
        have : (u : ℂ) = 1 := by simpa using hn.symm
        rw [this, map_one]; exact isUnit_one))
    (by
      have : omitted s (Om ℂ ℂ 0) = ⊥ := by
        unfold omitted
        rw [Submodule.span_eq_bot]
        rintro z ⟨j, _, _, _⟩
        exact j.elim0
      rw [this]; exact bot_le))

end GlobalTheory.W1.Ex
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MemMoveLevUloc
section
noncomputable section

namespace GlobalTheory.TwU

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open scoped TensorProduct

section Level

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  (S : StepLevel F E σ J T f bad)

def basePts : Subgroup (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) where
  carrier := {k | k ∈ levelAfL σ J S.Lb ∧ ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) k = 1}
  one_mem' := ⟨one_mem _, fun _ _ => map_one _⟩
  mul_mem' := fun ha hb => ⟨mul_mem ha.1 hb.1, fun v h => by rw [map_mul, ha.2 v h, hb.2 v h, mul_one]⟩
  inv_mem' := fun ha => ⟨inv_mem ha.1, fun v h => by rw [map_inv, ha.2 v h, inv_one]⟩

theorem mem_basePts_iff (k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : k ∈ basePts S ↔
    k ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧ (∀ v, bc (prV (E := E) v) k ∈ levelVL σ J v S.Lb) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) k = 1 := by
  rw [← and_assoc, ← GlobalTheory.LatticeStabLocal.mem_levelAfL_iff F E σ n J S.Lb S.Lb_fin k]
  rfl

variable {S} (k : basePts S)

def basePtU : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨k.1, k.2.1.1⟩

theorem basePt_loc (v : HeightOneSpectrum (𝓞 F)) : bc (prV (E := E) v) k.1 ∈ levelVL σ J v S.Lb :=
  ((mem_basePts_iff S k.1).1 k.2).2.1 v

theorem conj_mem_iff {G : Type} [Group G] {H : Subgroup G} {a : G} (ha : a ∈ H) (x : G) : a * x * a⁻¹ ∈ H ↔ x ∈ H := by
  rw [H.mul_mem_cancel_right (inv_mem ha), H.mul_mem_cancel_left ha]

def moveLev : StepLevel F E σ J T f bad :=
  { S with
    Uloc := fun v => (S.Uloc v).comap (MulAut.conj (bc (prV (E := E) v) k.1)).toMonoidHom
    Uloc_le := fun v x hx => (conj_mem_iff (H := UPts σ J (v.adicCompletion F)) (basePt_loc k v).1 x).1 (S.Uloc_le v hx)
    Uloc_lev := fun v x hx => (conj_mem_iff (basePt_loc k v) x).1 (S.Uloc_lev v hx)
    Uloc_hyp := fun v hv hT => by
      ext x
      rw [S.Uloc_hyp v hv hT]
      exact conj_mem_iff (basePt_loc k v) x
    UlocAlt := fun v h => by
      rw [← S.UlocAlt v h, k.2.2 v h]
      ext x
      simp
    U := S.U.comap (MulAut.conj k.1).toMonoidHom
    U_eq := fun x => by
      show k.1 * x * k.1⁻¹ ∈ S.U ↔ _
      rw [S.U_eq, conj_mem_iff (H := UPts σ J (FiniteAdeleRing (𝓞 F) F)) (a := k.1) (basePtU k).2]
      refine and_congr_right fun _ => forall_congr' fun v => ?_
      rw [map_mul, map_mul, map_inv]
      rfl
    U_compact := by
      letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
      haveI := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
      have hc : Continuous (fun x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) => k.1⁻¹ * x * k.1) :=
        (continuous_const.mul continuous_id).mul continuous_const
      convert S.U_compact.image hc using 1
      ext x
      constructor
      · intro hx
        exact ⟨k.1 * x * k.1⁻¹, hx, by group⟩
      · rintro ⟨y, hy, rfl⟩
        show k.1 * (k.1⁻¹ * y * k.1) * k.1⁻¹ ∈ S.U
        have e : k.1 * (k.1⁻¹ * y * k.1) * k.1⁻¹ = y := by group
        rwa [e]
    U_open := by
      letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
      haveI := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
      haveI : ContinuousMul (UPts σ J (FiniteAdeleRing (𝓞 F) F)) :=
        inferInstanceAs (ContinuousMul (UPts σ J (FiniteAdeleRing (𝓞 F) F)).toSubmonoid)
      have hc : Continuous (fun x : UPts σ J (FiniteAdeleRing (𝓞 F) F) => basePtU k * x * (basePtU k)⁻¹) :=
        (continuous_const.mul continuous_id).mul continuous_const
      exact S.U_open.preimage hc
    chi := S.chi.comp ((MulAut.conj k.1).toMonoidHom.subgroupComap S.U)
    chi_triv := fun x hx => S.chi_triv _ fun v hv => by
      show bc (prV (E := E) v) (k.1 * x.1 * k.1⁻¹) = 1
      rw [map_mul, map_mul, hx v hv, mul_one, ← map_mul, mul_inv_cancel, map_one] }

theorem mem_moveLev (x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : x ∈ (moveLev k).U ↔ k.1 * x * k.1⁻¹ ∈ S.U := Iff.rfl

def toMoved (κ : S.U) : (moveLev k).U :=
  ⟨k.1⁻¹ * κ.1 * k.1, by
    have e : k.1 * (k.1⁻¹ * κ.1 * k.1) * k.1⁻¹ = κ.1 := by group
    rw [mem_moveLev, e]
    exact κ.2⟩

theorem cls_move_iff (x y : UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    (Quotient.mk'' (x * basePtU k) : Cls (moveLev k)) = Quotient.mk'' (y * basePtU k) ↔
      (Quotient.mk'' x : Cls S) = Quotient.mk'' y := by
  refine (@DoubleCoset.eq _ _ _ _ _ _).trans (Iff.trans ?_ (@DoubleCoset.eq _ _ _ _ _ _).symm)
  refine exists_congr fun g => and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨κ, hκ, e⟩
    refine ⟨basePtU k * κ * (basePtU k)⁻¹, hκ, ?_⟩
    rw [← mul_inv_cancel_right y (basePtU k), e]
    group
  · rintro ⟨κ, hκ, e⟩
    refine ⟨(basePtU k)⁻¹ * κ * basePtU k, (toMoved k ⟨κ.1, hκ⟩).2, ?_⟩
    rw [e]
    group

theorem mem_hat_move_iff (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    (y⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S.Lb ↔
      ((y * k.1)⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F))
        (moveLev k).Lb := by
  rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  exact (inv_mem k.2.1).2 _

theorem map_conj_move (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    (moveLev k).U.map (MulAut.conj (y * k.1)).toMonoidHom = S.U.map (MulAut.conj y).toMonoidHom := by
  ext g
  constructor
  · rintro ⟨κ, hκ, e⟩
    refine ⟨_, (mem_moveLev k κ).1 hκ, Eq.trans ?_ e⟩
    show y * (k.1 * κ * k.1⁻¹) * y⁻¹ = y * k.1 * κ * (y * k.1)⁻¹
    group
  · rintro ⟨κ, hκ, e⟩
    refine ⟨_, (toMoved k ⟨κ, hκ⟩).2, Eq.trans ?_ e⟩
    show y * k.1 * (k.1⁻¹ * κ * k.1) * (y * k.1)⁻¹ = y * κ * y⁻¹
    group

theorem bij_move {cl : Type} {y : cl → UPts σ J (FiniteAdeleRing (𝓞 F) F)} (h : Function.Bijective fun c => (Quotient.mk'' (y c) : Cls S)) :
    Function.Bijective fun c => (Quotient.mk'' (y c * basePtU k) : Cls (moveLev k)) := by
  refine ⟨fun c c' e => h.1 ((cls_move_iff k _ _).1 e), fun q => ?_⟩
  induction q using Quotient.inductionOn' with
  | h x =>
    obtain ⟨c, hc⟩ := h.2 (Quotient.mk'' (x * (basePtU k)⁻¹))
    refine ⟨c, ?_⟩
    have h := (cls_move_iff k _ _).2 hc
    rwa [inv_mul_cancel_right] at h

end Level

section Chart

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {i : ℕ} {hi : i ≤ D.R.m} {cl : Type}
  {stab : cl → Type} [∀ c, Group (stab c)] {lat : cl → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)}


set_option maxHeartbeats 1000000 in
def moveChart (K : LevelChart D T bad i hi stab lat) (k : basePts K.lev) : LevelChart D T bad i hi stab lat where
  lev := moveLev k
  y := fun c => K.y c * basePtU k
  y_bij := bij_move k K.y_bij
  y_lat := fun c x => (K.y_lat c x).trans (mem_hat_move_iff k (K.y c).1 x)
  stabI := K.stabI
  stabI_inj := K.stabI_inj
  stabI_range := fun c γ => (K.stabI_range c γ).trans (SetLike.ext_iff.1 (map_conj_move k (K.y c).1) _).symm

end Chart

end GlobalTheory.TwU

end
end

