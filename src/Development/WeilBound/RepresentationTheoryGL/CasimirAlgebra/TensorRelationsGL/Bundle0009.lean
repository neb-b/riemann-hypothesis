module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PKTypeA
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle0007
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle0004

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PColAntiA
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace ColumnAntisymmetry

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

variable {m : ℕ} {E : Fin n → Fin n → Module.End ℂ M}

theorem deg_mono {d : ℕ} {g : Module.End ℂ (TV n M (Fin m))} (h : Deg E d g) :
    ∀ d', d ≤ d' → Deg E d' g := by
  induction h with
  | one d => intro d' _; exact Deg.one d'
  | add _ _ ih1 ih2 => intro d' h; exact Deg.add (ih1 d' h) (ih2 d' h)
  | smul c _ ih => intro d' h; exact Deg.smul c (ih d' h)
  | @om d g p _ ih =>
    intro d' h
    obtain ⟨k, rfl⟩ : ∃ k, d' = k + 1 := ⟨d' - 1, by omega⟩
    exact Deg.om p (ih k (by omega))
  | perm σ _ ih => intro d' h; exact Deg.perm σ (ih d' h)

theorem deg_mul {d d' : ℕ} {g h : Module.End ℂ (TV n M (Fin m))} (hg : Deg E d g) (hh : Deg E d' h) :
    Deg E (d + d') (g * h) := by
  induction hh with
  | one d' => rw [mul_one]; exact deg_mono hg _ (by omega)
  | add _ _ ih1 ih2 => rw [mul_add]; exact Deg.add ih1 ih2
  | smul c _ ih => rw [mul_smul_comm]; exact Deg.smul c ih
  | om p _ ih => rw [← mul_assoc]; exact Deg.om p ih
  | perm σ _ ih => rw [← mul_assoc]; exact Deg.perm σ ih

theorem deg_zero (d : ℕ) : Deg E d (0 : Module.End ℂ (TV n M (Fin m))) := by
  have := Deg.smul (E := E) (0 : ℂ) (Deg.one (P := Fin m) d)
  rwa [zero_smul] at this

theorem deg_sum {d : ℕ} (s : Finset (Fin m)) (f : Fin m → Module.End ℂ (TV n M (Fin m)))
    (hf : ∀ i ∈ s, Deg E d (f i)) : Deg E d (∑ i ∈ s, f i) := by
  classical
  exact Finset.sum_induction f (Deg E d) (fun _ _ ha hb => Deg.add ha hb) (deg_zero d) hf

theorem deg_xJ (j : Fin m) : Deg E 1 (xJ E j) := by
  unfold xJ
  refine Deg.add ?_ (deg_sum _ _ fun i _ => ?_)
  · have := Deg.om (E := E) j (Deg.one (P := Fin m) 0)
    rwa [one_mul] at this
  · have := Deg.perm (E := E) (Equiv.swap i j) (Deg.one (P := Fin m) 1)
    rwa [one_mul] at this

theorem deg_factor (i j : Fin m) (c : Prop) [Decidable c] :
    Deg E (if c then 1 else 0) (if c then xJ E i - xJ E j + 1 else 1) := by
  split_ifs
  · refine Deg.add ?_ (Deg.one 1)
    rw [sub_eq_add_neg]
    refine Deg.add (deg_xJ i) ?_
    have h1 := Deg.smul (-1 : ℂ) (deg_xJ (E := E) j)
    rwa [neg_one_smul] at h1
  · exact Deg.one 0

theorem deg_prod : ∀ (k : ℕ) (f : Fin k → Module.End ℂ (TV n M (Fin m))) (e : Fin k → ℕ),
    (∀ i, Deg E (e i) (f i)) → Deg E (∑ i, e i) (List.ofFn f).prod := by
  intro k
  induction k with
  | zero => intro f e _; simpa using Deg.one (E := E) (P := Fin m) 0
  | succ k ih =>
    intro f e hf
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact deg_mul (hf 0) (ih _ _ fun i => hf i.succ)

theorem npairs_eq (col : Fin m → ℕ) :
    (∑ j : Fin m, ∑ i : Fin m, if i < j ∧ col i = col j then 1 else 0) = npairs col := by
  unfold npairs
  rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]

theorem deg_colD {m : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (col : Fin m → ℕ) :
    Deg E (npairs col) (colD E col : Module.End ℂ (TV n M (Fin m))) := by
  have h := deg_prod m
    (fun j => (List.ofFn fun i : Fin m => if i < j ∧ col i = col j then xJ E i - xJ E j + 1 else 1).prod)
    (fun j => ∑ i : Fin m, if i < j ∧ col i = col j then 1 else 0)
    (fun j => deg_prod m _ _ (fun i => deg_factor i j _))
  rw [npairs_eq] at h
  exact h

end ColumnAntisymmetry

end PositivityTheory.Rg.Cz

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PContractB
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.CtrX

open PositivityTheory.Rg.Cz

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

def semiS {ι Γ : Type} [Fintype ι] (m : ℕ) (τ0 : ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (ρ : Γ → Module.End ℂ M) (c : ι → ℤ) : Submodule ℂ (TV n M (Fin m)) where
  carrier := {ζ | ∀ γ, actT (fun _ : Fin m => τ0) κ ρ γ ζ = (∏ τ, (κ τ γ).det ^ c τ) • ζ}
  add_mem' := by
    intro a b ha hb γ
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_add (f := _), ha γ, hb γ, smul_add]
  zero_mem' := by
    intro γ
    simp
  smul_mem' := by
    intro r a ha γ
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [map_smul, ha γ, smul_comm]

theorem prod_update_zpow {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ℂ) (c : ι → ℤ) (τ0 : ι) (hd : d τ0 ≠ 0) :
    ∏ τ, d τ ^ (Function.update c τ0 (c τ0 - 1)) τ = (d τ0)⁻¹ * ∏ τ, d τ ^ c τ := by
  have hsplit : ∀ f : ι → ℂ, ∏ τ, f τ = f τ0 * ∏ τ ∈ Finset.univ.erase τ0, f τ := by
    intro f
    rw [Finset.mul_prod_erase _ _ (Finset.mem_univ τ0)]
  rw [hsplit, hsplit (fun τ => d τ ^ c τ)]
  have hrest : ∏ τ ∈ Finset.univ.erase τ0, d τ ^ (Function.update c τ0 (c τ0 - 1)) τ = ∏ τ ∈ Finset.univ.erase τ0, d τ ^ c τ := by
    refine Finset.prod_congr rfl (fun τ hτ => ?_)
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hτ)]
  rw [hrest, Function.update_self, zpow_sub_one₀ hd]
  ring

theorem det_ne {ι Γ : Type} {bar : ι → ι} {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ} [Group Γ] [TopologicalSpace Γ]
    (hK : IsKD bar κ) (τ : ι) (γ : Γ) : (κ τ γ).det ≠ 0 := by
  exact Matrix.det_ne_zero_of_right_inverse (hK.unit τ γ)

theorem core (hQ : QdetFacts) (hW : WallAlg) (hT : TensorGK) (hL : LieInv)
    {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Group Γ] [TopologicalSpace Γ]
    {bar : ι → ι} {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ} {E : ι → Fin n → Fin n → Module.End ℂ M}
    {ρ : Γ → Module.End ℂ M} (hK : IsKD bar κ) (hG : IsGK bar κ E ρ) (τ0 : ι)
    {M0 : Type} [AddCommGroup M0] [Module ℂ M0] (q : M →ₗ[ℂ] M0) (F1 F2 : Fin n → Fin n → Module.End ℂ M0)
    (s : ℂ) (hF1 : GlRel F1) (hF2 : GlRel F2) (hc : ∀ a b c d, Commute (F1 a b) (F2 c d))
    (hs1 : HasChar F1 fun _ => s) (hs2 : HasChar F2 fun _ => s)
    (hq1 : ∀ a b, q ∘ₗ E τ0 a b = F1 a b ∘ₗ q) (hq2 : ∀ a b, q ∘ₗ E (bar τ0) a b = F2 a b ∘ₗ q)
    (hn : 1 ≤ n) (m : ℕ) (hm : 0 < m) (c : ι → ℤ) (ζ : TV n M (Fin m))
    (hζ : ∀ γ, actT (fun _ : Fin m => τ0) κ ρ γ ζ = (∏ τ, (κ τ γ).det ^ c τ) • ζ) (hz : ∃ I, q (ζ I) ≠ 0) :
    ∃ m2 < m, ∃ ζ2 : TV n M (Fin m2), (∀ γ, actT (fun _ : Fin m2 => τ0) κ ρ γ ζ2 =
      (∏ τ, (κ τ γ).det ^ (Function.update c τ0 (c τ0 - 1)) τ) • ζ2) ∧ ∃ I, q (ζ2 I) ≠ 0 := by
  classical
  obtain ⟨hGK, hcomm⟩ := hT n M ι Γ bar κ E ρ hK hG (Fin m) (fun _ => τ0)
  let χ : Γ → ℂ := fun γ => ∏ τ, (κ τ γ).det ^ c τ
  let Y : Submodule ℂ (TV n M (Fin m)) := semiS m τ0 κ ρ c
  have hY : ∀ y, y ∈ Y ↔ ∀ γ, actT (fun _ : Fin m => τ0) κ ρ γ y = χ γ • y := fun y => Iff.rfl
  let Q : TV n M (Fin m) →ₗ[ℂ] TV n M0 (Fin m) := LinearMap.compLeft q (Fin m → Fin n)
  have hQap : ∀ y I, Q y I = q (y I) := fun _ _ => rfl
  have hpmY : ∀ σ : Equiv.Perm (Fin m), ∀ y ∈ Y, pm σ y ∈ Y := by
    intro σ y hy
    rw [hY] at hy ⊢
    intro γ
    have h := congrArg (fun T : Module.End ℂ (TV n M (Fin m)) => T y) (hcomm σ (fun _ => rfl) γ).eq
    simp only [Module.End.mul_apply] at h
    rw [← h, hy γ, map_smul]
  have hOmY : ∀ j : Fin m, ∀ y ∈ Y, Om (E τ0) j y ∈ Y := by
    intro j y hy
    rw [hY] at hy ⊢
    intro γ
    rw [actT_Om τ0 κ (E τ0) ρ γ (hK.unit τ0 γ) (hG.ad γ τ0) j y, hy γ, map_smul]
  have hQpm : ∀ (σ : Equiv.Perm (Fin m)) y, Q (pm σ y) = pm σ (Q y) := by
    intro σ y
    funext I
    rfl
  have hQlift : ∀ (B : Module.End ℂ M) (B' : Module.End ℂ M0), q ∘ₗ B = B' ∘ₗ q → ∀ y, Q (lift B y) = lift B' (Q y) := by
    intro B B' hB y
    funext I
    simp only [hQap, lift, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    exact LinearMap.congr_fun hB (y I)
  have hQeAt : ∀ (p : Fin m) (a b : Fin n) y, Q (eAt p a b y) = eAt p a b (Q y) := by
    intro p a b y
    funext I
    simp only [hQap, eAt, LinearMap.pi_apply]
    split_ifs <;> simp [hQap]
  have hQOm : ∀ (j : Fin m) y, Q (Om (E τ0) j y) = Om F1 j (Q y) := by
    intro j y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Om, LinearMap.sum_apply, map_sum, Module.End.mul_apply, hQeAt]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [hQlift _ _ (hq1 a b), hQeAt]
  have hfib1 : fib (fun _ : Fin m => τ0) τ0 = Finset.univ := by
    ext p
    simp [fib]
  have hfib2 : fib (fun _ : Fin m => τ0) (bar τ0) = ∅ := by
    ext p
    simp [fib, (hK.ne τ0).symm]
  let c' : ℂ := ((c τ0 - c (bar τ0) : ℤ) : ℂ)
  have hQtE : ∀ y ∈ Y, ∀ a b : Fin n, tE Finset.univ (fun a b => F1 a b + -F2 b a) a b (Q y) = if a = b then c' • Q y else 0 := by
    intro y hy a b
    have h := hL n (TV n M (Fin m)) ι Γ bar κ (fun τ => tE (fib (fun _ : Fin m => τ0) τ) (E τ)) (actT (fun _ : Fin m => τ0) κ ρ) hK hGK c y ((hY y).1 hy) τ0 a b
    simp only [hfib1, hfib2, tE, Finset.sum_empty, add_zero] at h
    have h' := congrArg Q h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, LinearMap.add_apply, map_add (f := _), LinearMap.sum_apply, map_sum, hQlift _ _ (hq1 a b), hQlift _ _ (hq2 b a)] at h'
    simp only [hQeAt] at h'
    have hl : ∀ (B1 B2 : Module.End ℂ M0) (v : TV n M0 (Fin m)), lift (B1 + -B2) v = lift B1 v - lift B2 v := by
      intro B1 B2 v
      funext I
      simp [lift, sub_eq_add_neg]
    simp only [tE, LinearMap.add_apply, hl, LinearMap.sum_apply]
    rw [sub_add_eq_add_sub, h']
    split_ifs <;> simp [c']
  let X : Submodule ℂ (TV n M0 (Fin m)) := Y.map Q
  have hζY : ζ ∈ Y := (hY ζ).2 hζ
  have hXne : X ≠ ⊥ := by
    obtain ⟨I, hI⟩ := hz
    intro hX
    have hmem : Q ζ ∈ X := Submodule.mem_map_of_mem hζY
    rw [hX, Submodule.mem_bot] at hmem
    exact hI (by rw [← hQap, hmem]; rfl)
  have hXpm : ∀ σ : Equiv.Perm (Fin m), ∀ ξ ∈ X, pm σ ξ ∈ X := by
    intro σ ξ hξ
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hξ
    rw [← hQpm]
    exact Submodule.mem_map_of_mem (hpmY σ y hy)
  have hXOm : ∀ j : Fin m, ∀ ξ ∈ X, Om F1 j ξ ∈ X := by
    intro j ξ hξ
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hξ
    rw [← hQOm]
    exact Submodule.mem_map_of_mem (hOmY j y hy)
  have hXtE : ∀ a b : Fin n, ∀ ξ ∈ X, tE Finset.univ (fun a b => F1 a b + -F2 b a) a b ξ = if a = b then c' • ξ else 0 := by
    intro a b ξ hξ
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hξ
    exact hQtE y hy a b
  obtain ⟨-, -, -, hgl2, hch2⟩ := hQ n M0 F2 hF2
  have hcomm12 : ∀ a b c d : Fin n, Commute (F1 a b) (-F2 d c) := fun a b c d => (hc a b d c).neg_right
  obtain ⟨-, hwall⟩ := hW n M0 F1 (fun a b => -F2 b a) hF1 hgl2 hcomm12 s (-((n : ℂ) - 1) - s) c' hs1 (hch2 _ hs2) m X hXne hXpm hXOm hXtE
  obtain ⟨hnm, ξ, hξX, hξalt⟩ := hwall hm
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hξX
  have hQalt : Q (alt (firstG m n) y) = alt (firstG m n) (Q y) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [alt, LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul, hQpm]
  let ζ' : TV n M (Fin m) := alt (firstG m n) y
  have hζ'Y : ζ' ∈ Y := by
    show (∑ σ ∈ firstG m n, ((Equiv.Perm.sign σ : ℤ) : ℂ) • pm σ) y ∈ Y
    rw [LinearMap.sum_apply]
    exact Submodule.sum_mem _ (fun σ _ => Submodule.smul_mem _ _ (hpmY σ y hy))
  have hanti : ∀ τ ∈ firstG m n, pm τ ζ' = ((Equiv.Perm.sign τ : ℤ) : ℂ) • ζ' := fun τ hτ => pm_alt_firstG τ hτ y
  have hnz : ∃ I, q (ζ' I) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hξalt
    rw [← hQalt]
    funext I
    rw [hQap]
    exact hcon I
  set e := splitE m n hnm with he
  let g : TV n M (Fin (m - n) ⊕ Fin n) := reIx e ζ'
  let F : TV n (TV n M (Fin (m - n))) (Fin n) := cur g
  have hFanti : ∀ σ : Equiv.Perm (Fin n), pm σ F = ((Equiv.Perm.sign σ : ℤ) : ℂ) • F := cur_anti hnm ζ' hanti
  refine ⟨m - n, by omega, F id, fun γ => ?_, ?_⟩
  · have h1 : actT (fun _ : Fin (m - n) ⊕ Fin n => τ0) κ ρ γ g = χ γ • g := by
      have h0 := actT_reIx e (fun _ : Fin m => τ0) κ ρ γ ζ'
      rw [(hY ζ').1 hζ'Y γ, reIx_smul] at h0
      exact h0
    have h2 : (fun _ : Fin (m - n) ⊕ Fin n => τ0) = Sum.elim (fun _ : Fin (m - n) => τ0) (fun _ : Fin n => τ0) := by
      funext x
      cases x <;> rfl
    have h3 : actT (fun _ : Fin n => τ0) κ (actT (fun _ : Fin (m - n) => τ0) κ ρ) γ F = χ γ • F := by
      apply unc_inj
      rw [← actT_unc, unc_smul, unc_cur, ← h2, h1]
    have h4 := actT_anti_id τ0 κ (actT (fun _ : Fin (m - n) => τ0) κ ρ) γ F hFanti
    rw [h3] at h4
    have hdet := det_ne hK τ0 γ
    rw [prod_update_zpow (fun τ => (κ τ γ).det) c τ0 hdet, mul_smul]
    have h5 := congrArg (fun v => ((κ τ0 γ).det)⁻¹ • v) h4
    simp only [smul_smul, inv_mul_cancel₀ hdet, one_smul, Pi.smul_apply] at h5
    rw [← h5, smul_smul]
  · obtain ⟨I, hI⟩ := hnz
    let K : Fin (m - n) → Fin n := fun k => I (e.symm (Sum.inl k))
    let J : Fin n → Fin n := fun j => I (e.symm (Sum.inr j))
    obtain ⟨a, ha⟩ := anti_span F hFanti J
    refine ⟨K, fun hK0 => hI ?_⟩
    have hIe : Sum.elim K J ∘ e = I := by
      funext x
      simp only [Function.comp_apply]
      generalize hy : e x = w
      cases w with
      | inl k =>
        show I (e.symm (Sum.inl k)) = I x
        rw [← hy, Equiv.symm_apply_apply]
      | inr k =>
        show I (e.symm (Sum.inr k)) = I x
        rw [← hy, Equiv.symm_apply_apply]
    have h6 : ζ' I = F J K := by
      show ζ' I = ζ' (Sum.elim K J ∘ e)
      rw [hIe]
    rw [h6, ha, Pi.smul_apply, map_smul, hK0, smul_zero]

end PositivityTheory.Rg.Cz.CtrX

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PKType
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

open KTy in
theorem kType_of : TensorGl → TransAll → TensorGK → SphAll → Young → KType := by
  intro hGl hTr hGK hSph hY n hn M _ _ ι _ _ Γ _ _ _ _ _ bar κ E ρ hK hG l hl hc ℓ hℓ hW
  obtain ⟨s, w, nu, hnu, hm⟩ := sort_data l hl
  obtain ⟨H, hH⟩ := half bar hK.invol hK.ne
  set lab := lab3 bar (labQ nu) (tl H) with hlab
  have hlabcol : ∀ p q, colF nu H p = colF nu H q → lab p = lab q := fun p q h => colF_lab nu H bar p q h
  have htab := isTabF nu H hm
  let co : Pos nu H → Fin n := fun p => w (lab p) (bF nu H p)
  have hco : ∀ p q, colF nu H p = colF nu H q → co p = co q → p = q := by
    intro p q h h'
    refine htab.1 p q h ?_
    simp only [co, hlabcol p q h] at h'
    exact (w (lab q)).injective h'
  obtain ⟨S, hSA, hS0, hSe⟩ := hTr n M ι E hG.gl hG.comm l hc ℓ hℓ hW (Pos nu H) lab (Col ι n) (colF nu H) (bF nu H)
    co hlabcol htab hco
  have hGK' := hGK n M ι Γ bar κ E ρ hK hG (Pos nu H) lab
  have heig : ∀ τ (u : ℂ), (ℓ ∘ₗ cA (colF nu H) (bF nu H) ∘ₗ S) ∘ₗ qdet (tE (fib lab τ) (E τ)) u =
      ((u + (s : ℂ)) ^ n) • (ℓ ∘ₗ cA (colF nu H) (bF nu H) ∘ₗ S) := by
    intro τ u
    rw [hSe τ u]
    congr 1
    rw [← Fin.prod_const n (u + (s : ℂ))]
    refine Finset.prod_congr rfl fun k _ => ?_
    have e1 : (Finset.univ.filter fun p => lab p = τ ∧ co p = k) =
        Finset.univ.filter fun p => lab p = τ ∧ bF nu H p = (w τ).symm k := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, co]
      constructor
      · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩; rw [← h2, h1]; simp
      · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩; rw [h2, h1]; simp
    have e2 : (Finset.univ.filter fun p => lab p = τ ∧ bF nu H p = (w τ).symm k).card =
        nu τ ((w τ).symm k) + ((w τ).symm k : ℕ) := cntF nu H bar hK.invol hH τ ((w τ).symm k)
    have e3 := hnu τ ((w τ).symm k)
    rw [Equiv.apply_symm_apply] at e3
    rw [e1, e2]
    have e4 : ((nu τ ((w τ).symm k) + ((w τ).symm k : ℕ) : ℕ) : ℤ) = s - l τ k := by push_cast; linarith
    have e5 : ((nu τ ((w τ).symm k) + ((w τ).symm k : ℕ) : ℕ) : ℂ) = (s : ℂ) - (l τ k : ℂ) := by exact_mod_cast e4
    rw [e5]; ring
  obtain ⟨ξ, hξ, w', hw', hφ⟩ := hSph n hn (TV n M (Pos nu H)) ι Γ bar κ (fun τ => tE (fib lab τ) (E τ))
    (actT lab κ ρ) hK hGK'.1 s _ hS0 heig
  have hcomm : ∀ σ : Equiv.Perm (Pos nu H), (∀ p, lab (σ p) = lab p) →
      ∀ x ∈ envAlg (fun τ => tE (fib lab τ) (E τ)), Commute (pm σ) x := by
    intro σ hσ x hx
    refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx ?_
    rintro _ ⟨τ, a, b, rfl⟩
    exact (hGl n M (Pos nu H) (E τ) (hG.gl τ) (fib lab τ)).2.2.1 σ (by intro p; simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and, hσ]) a b
  have hGc : ∀ σ ∈ colG (colF nu H), ∀ p, lab (σ p) = lab p := by
    intro σ hσ p
    simp only [colG, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    exact hlabcol _ _ (hσ p)
  have hPc : ∀ σ ∈ colG (tl H), ∀ p, lab (dbl (Q := Fin (Fintype.card (Bx nu))) σ p) = lab p := by
    intro σ hσ p
    simp only [colG, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    rcases p with p | k | k <;> simp [dbl, hlab, lab3, hσ]
  have hA1 : ∀ x ∈ envAlg (fun τ => tE (fib lab τ) (E τ)), Commute (alt (colG (colF nu H))) x := fun x hx =>
    alt_comm _ _ fun σ hσ => hcomm σ (hGc σ hσ) x hx
  have hA2 : ∀ x ∈ envAlg (fun τ => tE (fib lab τ) (E τ)), Commute (altPair (Q := Fin (Fintype.card (Bx nu))) (tl H)) x := by
    intro x hx
    unfold altPair
    exact Commute.sum_left _ _ _ fun σ hσ => (hcomm _ (hPc σ hσ) x hx).smul_left _
  refine ⟨s, Fintype.card (Bx nu), Fintype.card (Pr H n), labQ nu, colQ nu, bQ nu, tl H,
    alt (colG (colF nu H)) ξ, ?_, isTabQ nu hm, ?_, ?_, ?_, ?_, ?_⟩
  · intro p p' h
    exact hlabcol (.inl p) (.inl p') (by simp [colF, h])
  · intro k k' h
    have h1 := (eP H n k).1.2
    have h2 := (hH (tl H k')).1 (eP H n k').1.2
    exact h2 (by rw [← h]; exact h1)
  · intro τ
    refine ⟨w τ, fun i => ?_⟩
    rw [cntQ, hnu]; ring
  · intro γ
    have := alt_comm (colG (colF nu H)) (actT lab κ ρ γ) fun σ hσ => hGK'.2 σ (hGc σ hσ) γ
    show actT lab κ ρ γ (alt _ ξ) = _
    rw [← Module.End.mul_apply, ← this.eq, Module.End.mul_apply, hξ]
  · intro p p' h hne
    have e := pm_mul_alt (M := M) (n := n) (colG (colF nu H)) (Equiv.swap (Sum.inl p) (Sum.inl p')) ?_
    · rw [← Module.End.mul_apply, e, Equiv.Perm.sign_swap (by simpa using hne)]
      simp
    · intro σ
      simp only [colG, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.Perm.mul_apply]
      have hs : ∀ x, colF nu H (Equiv.swap (Sum.inl p) (Sum.inl p') x) = colF nu H x := by
        intro x
        rcases eq_or_ne x (.inl p) with rfl | h1
        · simp [colF, h]
        rcases eq_or_ne x (.inl p') with rfl | h2
        · simp [colF, h]
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      simp only [hs]
  · intro h0
    apply hφ
    have e : altPair (tl H) (alt (colG (colF nu H)) (S (w' ξ))) =
        S (w' (altPair (tl H) (alt (colG (colF nu H)) ξ))) := by
      rw [← Module.End.mul_apply (alt _) S, (hA1 S hSA).eq, Module.End.mul_apply,
        ← Module.End.mul_apply (alt _) w', (hA1 w' hw').eq, Module.End.mul_apply,
        ← Module.End.mul_apply (altPair _) S, (hA2 S hSA).eq, Module.End.mul_apply,
        ← Module.End.mul_apply (altPair _) w', (hA2 w' hw').eq, Module.End.mul_apply]
    have hy := hY n M ι (Fin (Fintype.card (Bx nu))) (Fintype.card (Pr H n)) (tl H) (Col ι n) (colF nu H) (bF nu H) htab
      (fun p k => by rcases k with k | k <;> simp [colF]) (fun k k' => by simp [colF])
      (fun k k' => by simp [colF, bF, Prod.ext_iff]) (fun k k' => by simp [colF, bF, Prod.ext_iff])
      (S (w' ξ)) (by rw [e, h0]; simp)
    simp [hy]

end PositivityTheory.Rg.Cz

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTensorGK
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

theorem tensorGK_of : TensorGl → TensorGK := by
  intro hT n M _ _ ι _ _ Γ _ _ bar κ E ρ hK hE P _ _ lab
  refine ⟨⟨fun τ => (hT n M P (E τ) (hE.gl τ) (fib lab τ)).1, fun τ τ' h a b c d => TGK.tE_comm E hE.comm lab τ τ' h a b c d,
    TGK.actT_one lab κ ρ hK.one hE.one, TGK.actT_mul lab κ ρ hK.mul hE.mul,
    fun γ τ a b => TGK.actT_ad lab κ E ρ hK.unit hE.ad γ τ a b, fun y => TGK.actT_fin lab κ ρ hE.fin y,
    fun y lam => TGK.actT_cont lab κ ρ hK.cont hE.cont y lam, ?_⟩,
    fun σ hσ γ => TGK.pm_actT lab κ ρ σ hσ γ⟩
  intro τ X hX
  obtain ⟨c, hc0, hd, hoth, hρ⟩ := hE.der τ X hX
  exact ⟨c, hc0, hd, hoth, fun y lam => TGK.actT_der lab κ E ρ bar τ (hK.ne τ) hE.one hK.one hK.conj X c hc0 hd hoth
    hρ y lam⟩

end PositivityTheory.Rg.Cz

end
end

