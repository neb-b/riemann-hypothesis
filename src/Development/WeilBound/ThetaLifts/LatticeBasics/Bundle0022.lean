module

public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0009
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.IndicatorMem
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfActs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.WeilBound.ThetaLifts.LatticeBasics.SliceSeminorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsEqAdelicCharMul
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.ThConstInv
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.TC

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open GlobalTheory.SplitFlip PositivityTheory.KCo
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n' d : ℕ}

def SplitModel : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v),
      (∀ h₀ : GL (Fin d) (Fv F v), ∃ h ∈ UAt σ W (evFin F v), (mat h).map (piW t) = h₀) ∧
      ∃ ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ),
        Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _) ∧
        (∀ g ∈ UAt σ X (evFin F v), ∃ g₀, Reads v ι (om (g, 1)) (omB (chrW χW t) (chrW χX t) g₀ 1)) ∧
        ∀ h ∈ UAt σ W (evFin F v), ∀ h₀ : GL (Fin d) (Fv F v), (mat h).map (piW t) = h₀ →
          Reads v ι (om (1, h)) (omB (chrW χW t) (chrW χX t) 1 h₀)

theorem exists_inv' {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {ι : (X → ℂ) →ₗ[ℂ] (Y → ℂ)}
    (hb : Set.BijOn ι (SB X : Set _) (SB Y : Set _)) : ∃ j : (Y → ℂ) →ₗ[ℂ] (X → ℂ),
      (∀ Φ ∈ SB Y, j Φ ∈ SB X ∧ ι (j Φ) = Φ) ∧ ∀ φ ∈ SB X, j (ι φ) = φ := by
  obtain ⟨q, hq⟩ := (ι ∘ₗ (SB X).subtype).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 fun a b h =>
    Subtype.ext (hb.2.1 a.2 b.2 h))
  have k : ∀ φ ∈ SB X, (q (ι φ)).1 = φ := fun φ h => congrArg Subtype.val (LinearMap.congr_fun hq ⟨φ, h⟩)
  refine ⟨(SB X).subtype ∘ₗ q, fun Φ h => ⟨(q Φ).2, ?_⟩, k⟩
  obtain ⟨φ, h1, rfl⟩ := hb.2.2 h
  exact congrArg ι (k φ h1)

theorem intersection_update_fsHerm_neg_one {κ : Type} [Fintype κ] (v : Pl F) (f : SInf F κ) {φ : ∀ u : Pl F, (κ → Fv F u) → ℂ} (h1 : ∀ u, φ u ∈ SB _)
    (h2 : ∀ᶠ u in cofinite, φ u = Set.indicator {x | ∀ i, x i ∈ u.adicCompletionIntegers F} 1) :
    ∃ T : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ), (∀ ψ, T ψ = pure f (Function.update φ v ψ)) ∧
      (∀ ψ ∈ SB _, T ψ ∈ schA F κ) ∧ ∀ S, ∀ ψ ∈ SB _, ∀ ψ₁, Acts (evFin F v) S ψ ψ₁ → S (T ψ) = T ψ₁ := by
  obtain ⟨r, hr, hr'⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ h2
  have m : ∀ ψ ∈ SB _, tens (evFin F v) ψ r ∈ schA F κ := fun ψ hψ => by
    rw [hr']
    refine PositivityTheory.KCo.pure_mem_schA f _ (fun u => ?_) (GlobalTheory.PureFactor.update_eventually φ v ψ h2)
    by_cases hu : u = v
    · subst hu; rwa [Function.update_self]
    · rw [Function.update_of_ne hu]; exact h1 u
  exact ⟨{ toFun := fun ψ => tens (evFin F v) ψ r, map_add' := fun _ _ => funext fun _ => add_mul _ _ _
           map_smul' := fun _ _ => funext fun _ => mul_assoc _ _ _ }, hr', m, fun S ψ hψ ψ₁ h => h r ⟨hr, m ψ hψ⟩⟩

theorem acts_of_reads {v : Pl F} {ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)} {S R}
    (h : Reads v ι S R) {j : (Matrix (Fin n) (Fin d) (Fv F v) → ℂ) →ₗ[ℂ] ((Fin n × Fin d → Fv F v) → ℂ)}
    (h2 : ∀ φ ∈ SB _, j (ι φ) = φ) {φ} (hφ : φ ∈ SB _) : j (R (ι φ)) ∈ SB _ ∧ Acts (evFin F v) S φ (j (R (ι φ))) := by
  obtain ⟨φ₁, a, b, c⟩ := h φ hφ
  rw [← c, h2 φ₁ a]
  exact ⟨a, b⟩

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem apow_real (x : kˣ) (m : ℕ) : ∃ r : ℝ, 0 < r ∧ apow x ((m : ℂ) / 2) = r :=
  ⟨GlobalTheory.SplitWeil.nabs k x ^ ((m : ℝ) / 2), Real.rpow_pos_of_pos (GlobalTheory.SplitWeil.nabs_pos k x) _, by
    rw [Complex.ofReal_cpow (GlobalTheory.SplitWeil.nabs_pos k x).le]; simp [apow]⟩

theorem omB_right (ν α : kˣ →* ℂˣ) (h : GL (Fin d) k) (Φ : Matrix (Fin n) (Fin d) k → ℂ) :
    omB ν α 1 h Φ = ((α (gdet h) : ℂ) * apow (gdet h) ((n : ℂ) / 2)) • fun Y => Φ (Y * h.1) := funext fun Y => by
  simp [omB, gdet]

theorem omB_left (ν α : kˣ →* ℂˣ) (g : GL (Fin n) k) (Φ : Matrix (Fin n) (Fin d) k → ℂ) :
    omB ν α g 1 Φ = ((ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2)) • fun Y => Φ (g.1ᵀ * Y) := funext fun Y => by
  simp [omB, gdet]

theorem sb_star {A : Type} [TopologicalSpace A] {f : A → ℂ} (h : f ∈ SB A) : star f ∈ SB A :=
  ⟨h.1.comp star, h.2.comp_left (g := star) (star_zero _)⟩

end Loc

variable {B : Base F E} {X : Spc F E n} {X' : Spc F E n'} {W : Spc F E d} {M' : Model σ X' W}

theorem inv_loc (hL : LocDist) (e : Fin n ⊕ Fin n' ≃ Fin d) (hM' : M'.IsGood B.ψ) {v : Pl F} {om : Rep σ X W} {om' : Rep σ X' W}
    {ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)}
    {ι' : ((Fin n' × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n') (Fin d) (Fv F v) → ℂ)}
    (b : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _))
    (b' : Set.BijOn ι' (SB (Fin n' × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n') (Fin d) (Fv F v)) : Set _))
    {ν ν' α α' : (Fv F v)ˣ →* ℂˣ} (n1 : ∀ x, ‖(ν x : ℂ)‖ = 1) (n2 : ∀ x, ‖(α x : ℂ)‖ = 1) (hν : ∀ x, ν x = α x / α' x)
    (hne : ν (unifAt v) ≠ 1) (L : Fn F n' d →ₗ[ℂ] Fn F n d →ₛₗ[starRingEnd ℂ] ℂ)
    (hh : ∀ h₀, ∃ h, Reads v ι (om (1, h)) (omB ν α 1 h₀) ∧ Reads v ι' (om' (1, h)) (omB ν' α' 1 h₀) ∧
      ∀ Φ ∈ PolData B M', ∀ Ψ ∈ schA F _, L (om' (1, h) Φ) (om (1, h) Ψ) = L Φ Ψ)
    {u g₀} (hu : Reads v ι (om (u, 1)) (omB ν α g₀ 1)) : ∀ Φ ∈ PolData B M', ∀ Ψ ∈ schA F _, L Φ (om (u, 1) Ψ) = L Φ Ψ := by
  obtain ⟨j, j1, j2⟩ := exists_inv' b
  obtain ⟨j', j1', j2'⟩ := exists_inv' b'
  intro Φ hΦ Ψ hΨ
  refine LinearMap.eqOn_span' (f := L.flip (om (u, 1) Ψ)) (g := L.flip Ψ) ?_ hΦ
  rintro _ ⟨f', hf', φ', p1', p2', rfl⟩
  refine schA_le (LinearMap.eqLocus (L (pure f' φ') ∘ₛₗ om (u, 1)) (L (pure f' φ'))) (fun f φ p1 p2 => ?_) hΨ
  obtain ⟨T, t1, t2, t3⟩ := intersection_update_fsHerm_neg_one v f p1 p2
  obtain ⟨T', t1', -, t3'⟩ := intersection_update_fsHerm_neg_one v f' p1' ((p2'.and hM'.std).mono fun _ h => h.1.trans h.2)
  have t2' : ∀ ψ ∈ SB _, T' ψ ∈ PolData B M' := fun ψ hψ => Submodule.subset_span ⟨f', hf', _, fun w => by
    by_cases hw : w = v
    · subst hw; rwa [Function.update_self]
    · rw [Function.update_of_ne hw]; exact p1' w, by
      filter_upwards [p2', eventually_cofinite_ne v] with w h hw using (Function.update_of_ne hw _ _).trans h, t1' ψ⟩
  let N : (Fv F v)ˣ →* ℂˣ := MonoidHom.toHomUnits ⟨⟨fun x => apow x ((d : ℂ) / 2), apow_one _⟩, fun x y => apow_mul x y _⟩
  have hN : ∀ x, ((ν * N⁻¹) x : ℂ) = ν x * (apow x ((d : ℂ) / 2))⁻¹ := fun x => by simp [N]
  have cj : ∀ {z : ℂ}, ‖z‖ = 1 → starRingEnd ℂ z = z⁻¹ := fun h => (Complex.inv_eq_conj h).symm
  have cj' : ∀ (x : (Fv F v)ˣ) (m : ℕ), starRingEnd ℂ (apow x ((m : ℂ) / 2)) = apow x ((m : ℂ) / 2) := fun x m => by
    obtain ⟨r, -, h⟩ := apow_real x m
    rw [h, Complex.conj_ofReal]
  let β : SB (Matrix (Fin n) (Fin d) (Fv F v)) →ₗ[ℂ] SB (Matrix (Fin n') (Fin d) (Fv F v)) →ₗ[ℂ] ℂ :=
    LinearMap.mk₂ ℂ (fun a b => L (T' (j' b.1)) (T (j (star a.1)))) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp) fun _ _ _ => by simp
  let g₁ := Matrix.GeneralLinearGroup.mkOfDetNeZero g₀.1ᵀ (by rw [Matrix.det_transpose]; exact g₀.det_ne_zero)
  have key := locBil hL v e (ν * N⁻¹) (fun t ht h => hne (Units.ext ?_)) β (fun a b h₀ => ?_)
    ⟨_, sb_star (b.1 (p1 v))⟩ ⟨_, b'.1 (p1' v)⟩ g₁
  · have k2 := t3 _ _ (p1 v) _ (acts_of_reads hu j2 (p1 v)).2
    rw [omB_left, map_smul, map_smul, t1, Function.update_eq_self] at k2
    change L _ (T (j (star fun y => star (ι (φ v) (g₀.1ᵀ * y))))) = _ * L _ (T (j (star (star _)))) at key
    rw [star_star, j2 _ (p1 v), j2' _ (p1' v), t1', t1 (φ v), Function.update_eq_self, Function.update_eq_self, hN,
      show Matrix.GeneralLinearGroup.det g₁ = gdet g₀ from Units.ext (Matrix.det_transpose _), ← Pi.star_def, star_star] at key
    change L _ (om (u, 1) _) = _
    rw [k2, map_smulₛₗ, key, map_mul, cj (n1 _), cj', smul_eq_mul]
    have := apow_ne_zero (gdet g₀) ((d : ℂ) / 2)
    field_simp
  · obtain ⟨r, hr, e1⟩ := apow_real (unifAt v) d
    rw [hN, e1, mul_inv_eq_iff_eq_mul₀ (by exact_mod_cast hr.ne'), ← Complex.ofReal_mul] at h
    have := n1 (unifAt v)
    rw [h, Complex.norm_real, Real.norm_of_nonneg (mul_pos ht hr).le] at this
    rw [h, this]; rfl
  · obtain ⟨h, r1, r2, r3⟩ := hh h₀
    have a1 := j1 _ (sb_star a.2)
    have b1 := j1' _ b.2
    have k1 := t3 _ _ a1.1 _ (acts_of_reads r1 j2 a1.1).2
    have k2 := t3' _ _ b1.1 _ (acts_of_reads r2 j2' b1.1).2
    have k3 := r3 _ (t2' _ b1.1) _ (t2 _ a1.1)
    rw [k1, k2, a1.2, b1.2, omB_right, omB_right] at k3
    simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, cj (n2 _), cj'] at k3
    have hd : (d : ℂ) / 2 = (n : ℂ) / 2 + (n' : ℂ) / 2 := by
      have := Fintype.card_congr e
      simp only [Fintype.card_sum, Fintype.card_fin] at this
      rw [← this]; push_cast; ring
    change L (T' (j' fun y => b.1 (y * h₀.1))) (T (j fun y => star a.1 (y * h₀.1))) = _ * L (T' (j' b.1)) (T (j (star a.1)))
    rw [← k3, hN, hν, hd, apow_add]
    have := apow_ne_zero (gdet h₀) ((n : ℂ) / 2)
    have := apow_ne_zero (gdet h₀) ((n' : ℂ) / 2)
    simp only [Units.val_div_eq_div_val]
    field_simp

end GlobalTheory.ThK.Dbl.TC

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.ThetaBox
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Automorphic.GJMatrix GroundTheory.Global

attribute [local instance 100000] measurableSpace_adeleRing

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}
  {Φ : (κ ⊕ κ → AF F) → ℂ}

theorem sl_int (h : Φ ∈ schA F (κ ⊕ κ)) (a) : Integrable (sl a Φ) (adeleMeasurePi F) :=
  integrable_of_mem_schwartzBruhatPi ((sl_mem h).1 a)


variable (F κ) in
def lD : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] ℂ := (LinearMap.exists_extend
  ({ toFun Φ := adelicFourierPi F (sl 0 Φ.1) 0
     map_add' Φ Ψ := congrFun (adelicFourierPi_add (sl_int Φ.2 0) (sl_int Ψ.2 0)) 0
     map_smul' c Φ := congrFun (adelicFourierPi_smul c (sl 0 Φ.1)) 0 } : schA F (κ ⊕ κ) →ₗ[ℂ] ℂ)).choose

theorem lD_apply (h : Φ ∈ schA F (κ ⊕ κ)) : lD F κ Φ = adelicFourierPi F (sl 0 Φ) 0 :=
  LinearMap.congr_fun (LinearMap.exists_extend _).choose_spec (⟨Φ, h⟩ : schA F (κ ⊕ κ))

theorem lD_int (h : Φ ∈ schA F (κ ⊕ κ)) : lD F κ Φ = ∫ u, Φ (Sum.elim u u) ∂adeleMeasurePi F := by
  rw [lD_apply h]; simp [adelicFourierPi, sl]

theorem lD_adm : lD F κ ∈ (adeleClass F).adm (κ ⊕ κ) := fun g hg => by
  refine ⟨finiteFourierPi F (fun u => g (Sum.elim (u + finPartPi (K := F) 0) u)) (finPartPi 0) •
    ((BoundedContinuousFunction.evalCLM ℂ (infPartPi 0)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)).comp
      ((mixedFourierPiSchwartz F).comp (slice (infPartPi (K := F) 0))), fun f => ?_⟩
  rw [lD_apply (Submodule.subset_span ⟨f, g, hg, rfl⟩), show pureA F f g = schwartzBruhatTensorPi f g from rfl,
    sl_tensor, adelicFourierPi_schwartzBruhatTensorPi]
  exact mul_comm _ _

theorem std_eq (h : IsStd ψ) : ∃ ξ : F, ξ ≠ 0 ∧ ∀ x, ψ x = (adelicChar F (algebraMap F (AF F) ξ * x) : ℂ) := by
  obtain ⟨ξ, e⟩ := GlobalTheory.CompanionTheory.AdeleDual.exists_eq_adelicChar_mul ψ h.1 h.2.1
  obtain ⟨x, hx⟩ := GlobalTheory.StdCharFromIsStd.exists_ne_one h
  exact ⟨ξ, fun h0 => hx (by simp [e, h0]), e⟩

theorem elim_dot (a a' b b' : κ → AF F) : Sum.elim a a' ⬝ᵥ Sum.elim b b' = a ⬝ᵥ b + a' ⬝ᵥ b' := by
  simp [dotProduct, Fintype.sum_sum_type]

theorem lD_schr (h : IsStd ψ) {ξ : F} (e : ∀ x, ψ x = (adelicChar F (algebraMap F (AF F) ξ * x) : ℂ))
    (hΦ : Φ ∈ schA F (κ ⊕ κ)) (a a' b b' : κ → AF F) :
    lD F κ (schr ψ (Sum.elim a a', Sum.elim b b') Φ) = ψ (⅟(2 : AF F) * (a ⬝ᵥ b + a' ⬝ᵥ b') - a' ⬝ᵥ (b + b')) *
      adelicFourierPi F (sl (a - a') Φ) (algebraMap F (AF F) ξ • (b + b')) := by
  rw [lD_int (GlobalTheory.HeisSchA.schr_mem_schA ψ h _ Φ hΦ), adelicFourierPi, ← integral_const_mul, eq_comm,
    ← integral_add_right_eq_self _ a', eq_comm]
  refine integral_congr_ae (.of_forall fun u => ?_)
  have : ∑ i, (u + a') i * (algebraMap F (AF F) ξ • (b + b')) i = algebraMap F (AF F) ξ * ((u + a') ⬝ᵥ (b + b')) := by
    rw [← smul_eq_mul, ← dotProduct_smul]; rfl
  simp only [schr, sl]
  rw [this, ← e, mul_left_comm, ← AddChar.map_add_eq_mul, mul_comm]
  congr 2
  · funext i; cases i <;> simp
  · simp only [elim_dot, add_dotProduct, dotProduct_add]; ring

theorem lD_kill (h : IsStd ψ) (hΦ : Φ ∈ schA F (κ ⊕ κ)) (a b : κ → AF F) :
    lD F κ (schr ψ (Sum.elim a a, Sum.elim b (-b)) Φ) = lD F κ Φ := by
  obtain ⟨ξ, -, e⟩ := std_eq h
  rw [lD_schr h e hΦ, lD_apply hΦ]; simp

theorem lD_inj (h : IsStd ψ) (hΦ : Φ ∈ schA F (κ ⊕ κ))
    (h0 : ∀ a b, lD F κ (schr ψ (Sum.elim a 0, Sum.elim b 0) Φ) = 0) : Φ = 0 := by
  obtain ⟨ξ, hξ, e⟩ := std_eq h
  have k : ∀ a, adelicFourierPi F (sl a Φ) = 0 := fun a => funext fun b => by
    have := h0 a (algebraMap F (AF F) ξ⁻¹ • b)
    rw [lD_schr h e hΦ, sub_zero, add_zero, smul_smul, ← map_mul, mul_inv_cancel₀ hξ, map_one, one_smul] at this
    exact (mul_eq_zero.1 this).resolve_left (by rw [e]; exact Circle.coe_ne_zero _)
  funext z
  have := congrFun (adelicFourierPi_adelicFourierPi ((sl_mem hΦ).1 (z ∘ .inl - z ∘ .inr))) (-(z ∘ .inr))
  rw [k, adelicFourierPi_zero] at this
  simpa [sl] using this.symm

theorem lD_theta (h : IsStd ψ) (hΦ : Φ ∈ schA F (κ ⊕ κ)) :
    HasSum (fun p : (κ → F) × (κ → F) => lD F κ (schr ψ (Sum.elim (rt p.1) (-rt p.1), Sum.elim (rt p.2) (rt p.2)) Φ))
      (thetaSum F Φ) := by
  obtain ⟨ξ, hξ, e⟩ := std_eq h
  have h2 : ξ * 2 ≠ 0 := mul_ne_zero hξ two_ne_zero
  convert ((Equiv.smulRight (β := κ → F) (two_ne_zero (α := F))).prodCongr (Equiv.smulRight (β := κ → F) h2)).hasSum_iff.2
    (hasSum_sl hΦ) using 2 with p
  have : ⅟(2 : AF F) * (rt p.1 ⬝ᵥ rt p.2 + -rt p.1 ⬝ᵥ rt p.2) - -rt p.1 ⬝ᵥ (rt p.2 + rt p.2) =
      algebraMap F (AF F) (p.1 ⬝ᵥ (p.2 + p.2)) := by
    simp [dotProduct]
  rw [lD_schr h e hΦ, this, h.2.1, one_mul]
  congr 2 <;> funext i <;> simp [rt, map_ofNat] <;> ring

theorem star_mem {φ : (κ → AF F) → ℂ} (h : φ ∈ schA F κ) : star φ ∈ schA F κ :=
  (GlobalTheory.CompanionTheory.ThetaReal.thetaSum_star_and_schA_star F κ φ).2 h

theorem box_mem {φ φ' : (κ → AF F) → ℂ} (h : φ ∈ schA F κ) (h' : φ' ∈ schA F κ) : boxFun φ (star φ') ∈ schA F (κ ⊕ κ) :=
  GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ φ h _ (star_mem h')

theorem theta_box {φ φ' : (κ → AF F) → ℂ} (h : φ ∈ schA F κ) (h' : φ' ∈ schA F κ) :
    thetaSum F (boxFun φ (star φ')) = thetaSum F φ * star (thetaSum F φ') := by
  rw [show star (thetaSum F φ') = _ from (GlobalTheory.CompanionTheory.ThetaReal.thetaSum_star_and_schA_star F κ φ').1.symm, thetaSum, thetaSum,
    thetaSum, tsum_mul_tsum_of_summable_norm (summable_norm_of_mem_schA F h) (summable_norm_of_mem_schA F (star_mem h')),
    ← (Equiv.sumArrowEquivProdArrow κ κ F).tsum_eq]
  rfl

theorem borel_eq : (MeasurableSpace.pi : MeasurableSpace (κ → AF F)) = borel _ := BorelSpace.measurable_eq

theorem lD_haar (ν : @Measure (κ → AF F) (borel _)) (hν : @Measure.IsAddHaarMeasure _ _ _ (borel _) ν) :
    ∃ c : ℝ, 0 < c ∧ ∀ φ ∈ schA F κ, ∀ φ' ∈ schA F κ, lD F κ (boxFun φ (star φ')) = c * ∫ u, φ u * star (φ' u) ∂ν := by
  revert ν
  rw [← borel_eq]
  intro ν hν
  refine ⟨Measure.addHaarScalarFactor (adeleMeasurePi F) ν, Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _,
    fun φ h φ' h' => ?_⟩
  rw [lD_int (box_mem h h')]
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul (adeleMeasurePi F) ν, integral_smul_nnreal_measure]
  rfl

theorem lD_sq {φ : (κ → AF F) → ℂ} (h : φ ∈ schA F κ) :
    lD F κ (boxFun φ (star φ)) = (∫⁻ x, ‖φ x‖ₑ ^ 2 ∂adeleMeasurePi F).toReal := by
  rw [lD_int (box_mem h h)]
  have : ∀ u, boxFun φ (star φ) (Sum.elim u u) = ((‖φ u‖ ^ 2 : ℝ) : ℂ) := fun u => by
    simp [boxFun, Complex.mul_conj']
  simp only [this]
  rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (.of_forall fun _ => sq_nonneg _)
    ((continuous_of_mem_schwartzBruhatPi h).norm.pow 2).aestronglyMeasurable]
  simp [ENNReal.ofReal_pow, ofReal_norm_eq_enorm]

theorem lD_unit {G : Type} [Group G] {om : G →* Module.End ℂ ((κ → AF F) → ℂ)} (hu : IsUnitaryOn (adeleClass F) om)
    (hp : ∀ g, ∀ φ ∈ schA F κ, om g φ ∈ schA F κ) (g : G) {φ φ' : (κ → AF F) → ℂ} (h : φ ∈ schA F κ) (h' : φ' ∈ schA F κ) :
    lD F κ (boxFun (om g φ) (star (om g φ'))) = lD F κ (boxFun φ (star φ')) := by
  have k : ∀ φ ∈ schA F κ, lD F κ (boxFun (om g φ) (star (om g φ))) = lD F κ (boxFun φ (star φ)) := fun φ h => by
    unfold IsUnitaryOn at hu
    rw [← borel_eq] at hu
    rw [lD_sq h, lD_sq (hp g φ h), hu _ inferInstance g φ h]
  have k1 := k _ (add_mem h h')
  have k2 := k _ (add_mem h (Submodule.smul_mem _ Complex.I h'))
  simp only [map_add (f := _), map_smul, star_add, star_smul, GlobalTheory.SchwartzBox.boxFun_add_left, GlobalTheory.SchwartzBox.boxFun_add_right,
    GlobalTheory.SchwartzBox.boxFun_smul_left, GlobalTheory.SchwartzBox.boxFun_smul_right, k φ h, k φ' h', smul_eq_mul,
    Complex.star_def, Complex.conj_I] at k1 k2
  linear_combination (1 / 2) * k1 + (Complex.I / 2) * k2 + (1 / 2 * (lD F κ (boxFun (om g φ) (star (om g φ'))) -
    lD F κ (boxFun φ (star φ')) - lD F κ (boxFun (om g φ') (star (om g φ))) + lD F κ (boxFun φ' (star φ)))) * Complex.I_mul_I

end GlobalTheory.ThK.Dbl

end
end

