module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.RootOfUnityInt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.NatNotMemPv

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.DnIncInt0Of
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.IAT

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField Classical IsDedekindDomain Formalism.UG

variable {D : D7} {u : D.what₂.Word}

def DnLatLoc0 (T : Forms0 D u) : Prop :=
  ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v c (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)),
    g ((D.fm u).te 0 v c) = 1 →
    ∀ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
      (η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : T.cls0.lev.U),
      (∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) →
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
        (T.cls0.y ((D.fm u).dn 0 v c g)).1 = (T.cls0.y c).1 * η.1 * κ.1 →
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g))) =
        Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) →
      ∀ B B' B₂ : GL (Fin (D.R.N 0)) D.host.E,
        IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) B →
        IsLocBasis (D.mem u).A.T (Lk T.atT 0 (Nat.zero_le _) v c : Set _) B' →
        IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g) : Set _) B₂ →
        ∀ τ, IntInv w
          (atInf (embT D) (B₂⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ *
            atInf (embT D) ((γ.1⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ *
            (if τ = (D.fm u).tauOf w v then atInf (embT D) (B' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ
              else atInf (embT D) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ))

theorem tr_int (w : D.what₂.places.Pl) (T : Forms0 D u) (h : (D.mem u).C.Y 0 → ℂ)
    (g : GL (Fin (D.R.N 0)) D.host.E) (hg : g ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (M : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ) (hP : P ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam 0))
    (hPe : ∀ z, h z = fnOf _ (shiftOf (lamT u 0)) M P (T.val0.eY z))
    (Kt Ki : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ) (hK : ∀ τ, Ki τ * Kt τ = 1)
    (hN : ∀ τ, IntInv w (M τ * atInf (embT D) (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ * Ki τ)) :
    ∃ Q ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam 0), ∀ z,
      h (T.val0.eY.symm (frameTranslate (embT D) (fun τ x => embedding_conj_compat D τ x) g hg (T.val0.eY z))) =
        fnOf _ (shiftOf (lamT u 0)) Kt Q (T.val0.eY z) := by
  let N : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ := fun τ =>
    M τ * atInf (embT D) (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ * Ki τ
  have hMK : (fun τ => M τ * atInf (embT D) (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ) =
      fun τ => N τ * Kt τ := by
    funext τ
    simp only [N, Matrix.mul_assoc, hK τ, Matrix.mul_one]
  refine ⟨MvPolynomial.C (∏ τ, (N τ).det ^ shiftOf (lamT u 0) τ) * subP N P, ?_, fun z => ?_⟩
  · refine bwG_intSpan_allSubP D w _ N _ ?_ P hP
    intro τ f hf
    obtain ⟨N', h1, h2, h3⟩ := hN τ
    exact local_GL_stabilises_lattice D w _ _ _ _ N' h1 h2 h3 f hf
  · rw [hPe, Equiv.apply_symm_apply, PI.UnitaryGroupMassFormula.IAT.fnOf_tr, hMK, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.fnOf_mul]

private theorem embLL_smul_mem_intSpan_of_mem_intW (w : D.what₂.places.Pl) {n : ℕ} (lam : D.what₂.Tau → DomWeight n)
    (r : D.what₂.LL) (hr : r ∈ intW D.what₂.places w) {Q : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ}
    (hQ : Q ∈ Formalism.L2.Forms.IntSpan D w lam) : D.what₂.embLL r • Q ∈ Formalism.L2.Forms.IntSpan D w lam := by
  induction hQ using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨r', f, hr', hf, rfl⟩ := hp
    exact AddSubgroup.subset_closure ⟨r * r', f, mul_mem hr hr', hf, by rw [smul_smul, map_mul]⟩
  | zero => simp
  | add p q _ _ hp hq => rw [smul_add]; exact add_mem hp hq
  | neg p _ hp => rw [smul_neg]; exact neg_mem hp

theorem dnIncInt0_of (T : Forms0 D u) (hC : LocalLatticeBases.ChiFin0 T) (hL : DnLatLoc0 T) : DnIncInt0 T := by
  intro w hw hseen v c g hg h hh B B' hB hB'
  have hg0 : g ≠ 0 := by
    rintro rfl
    simp at hg
  obtain ⟨γ, η, κ, hη, hrel, hloc, -, htr⟩ := T.down_natural_level_zero v c g hg0
  obtain ⟨⟨B₂, hB₂⟩, -⟩ := bases0 T ((D.fm u).dn 0 v c g)
  obtain ⟨P, hP, hPe⟩ := hh B₂ hB₂
  obtain ⟨Q, hQ, hQe⟩ := tr_int w T h γ.1⁻¹
    ((UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))).inv_mem γ.2) _ P hP hPe
    (fun τ => if τ = (D.fm u).tauOf w v then atInf (embT D) (B'⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ
      else atInf (embT D) (B⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ)
    (fun τ => if τ = (D.fm u).tauOf w v then atInf (embT D) (B' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ
      else atInf (embT D) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ)
    (fun τ => by split_ifs <;> exact S0.at_infinity_mul_inv (embT D) _ τ)
    (hL w hw hseen v c g hg γ η κ hη hrel hloc B B' B₂ hB hB' hB₂)
  obtain ⟨r, hr, hre⟩ := chi_inv_int T hC w κ
  refine ⟨D.what₂.embLL r • Q, embLL_smul_mem_intSpan_of_mem_intW w _ r hr hQ, fun z => ?_⟩
  rw [htr h z (T.val0.eY.symm (frameTranslate (embT D) (fun τ x => embedding_conj_compat D τ x) γ.1⁻¹
    ((UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))).inv_mem γ.2) (T.val0.eY z))) ?_,
    hQe, LinearMap.map_smul, Pi.smul_apply, smul_eq_mul, hre]
  intro τ
  rw [Equiv.apply_symm_apply]
  show _ = _ * (_ * _)
  rw [← Matrix.mul_assoc, at_infinity_mul_inv, Matrix.one_mul]

end PI.UnitaryGroupMassFormula.IAT

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.IntInvOfLoc
section
noncomputable section

open NumberField Ideal Matrix

namespace PI.UnitaryGroupMassFormula.IAT

open Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Host Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.UG

variable {D : D7} {u : D.what₂.Word}

theorem le_locP' {E : Type} [Field E] [NumberField E] {n : ℕ} (P : Ideal (𝓞 E)) [P.IsPrime]
    (L : Submodule (𝓞 E) (Fin n → E)) : L ≤ Formalism.HermitianLatticesTheory.localization₂ P L := by
  unfold Formalism.HermitianLatticesTheory.localization₂ Formalism.HermitianLatticesTheory.locS
  intro x hx
  exact ⟨1, P.primeCompl.one_mem, by simpa using hx⟩

theorem localization_mono' {E : Type} [Field E] [NumberField E] {n : ℕ} (P : Ideal (𝓞 E)) [P.IsPrime]
    {L M : Submodule (𝓞 E) (Fin n → E)} (h : L ≤ M) : Formalism.HermitianLatticesTheory.localization₂ P L ≤ Formalism.HermitianLatticesTheory.localization₂ P M := by
  unfold Formalism.HermitianLatticesTheory.localization₂ Formalism.HermitianLatticesTheory.locS
  rintro x ⟨s, hs, hx⟩
  exact ⟨s, hs, h hx⟩

theorem intInv_of_loc (A : AtTTied u) (w : D.what₂.places.Pl) (hw : Formalism.MainNotions.product_first_zeroth_parts.OverT D u w)
    (hseen : (D.fm u).seenP w = true) (v : (D.mem u).A.vT) {n : ℕ} {X Y : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (Bx By g : GL (Fin n) D.host.E)
    (hBx : IsLocBasis (D.mem u).A.T (X : Set (Fin n → D.host.E)) Bx)
    (hBy : IsLocBasis (D.mem u).A.T (Y : Set (Fin n → D.host.E)) By)
    (h1 : Y ≤ Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat (g : Matrix (Fin n) (Fin n) D.host.E) X))
    (h2 : mulLat (g : Matrix (Fin n) (Fin n) D.host.E) X ≤ Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) Y) :
    IntInv w (atInf (embT D) ((Bx⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) ((D.fm u).tauOf w v) *
      atInf (embT D) ((g⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) ((D.fm u).tauOf w v) *
      atInf (embT D) (By : Matrix (Fin n) (Fin n) D.host.E) ((D.fm u).tauOf w v)) := by
  have hT1 : ¬ (D.mem u).A.T ∣ 1 := (D.mem u).A.T_prime.not_dvd_one
  have hcol : ∀ (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (B : GL (Fin n) D.host.E),
      IsLocBasis (D.mem u).A.T (L : Set (Fin n → D.host.E)) B → ∀ b : Fin n, ∃ s : ℕ,
        ¬ (D.mem u).A.T ∣ s ∧
          (s : D.host.E) • ((B : Matrix (Fin n) (Fin n) D.host.E) *ᵥ Pi.single b 1) ∈ L := by
    intro L B hB b
    refine (hB _).mpr ⟨1, hT1, fun a => ?_⟩
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Nat.cast_one, one_mul]
    by_cases h : a = b
    · subst h
      rw [Pi.single_eq_same]
      exact ⟨1, map_one _⟩
    · rw [Pi.single_eq_of_ne h]
      exact ⟨0, map_zero _⟩
  have hprime : ∀ (t : 𝓞 D.host.E) (s : ℕ), t ∉ A.Pv v → ¬ (D.mem u).A.T ∣ s →
      t * (s : 𝓞 D.host.E) ∉ A.Pv v := by
    intro t s ht hs hmem
    rcases (inferInstance : (A.Pv v).IsPrime).mem_or_mem hmem with h | h
    · exact ht h
    · exact nat_not_mem_Pv A v s hs h
  have hsmul : ∀ (t : 𝓞 D.host.E) (s : ℕ) (z : Fin n → D.host.E),
      (t * (s : 𝓞 D.host.E)) • z = t • ((s : D.host.E) • z) := by
    intro t s z
    rw [mul_smul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  have hN : ∀ a b, embT D ((D.fm u).tauOf w v)
      ((((Bx⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *
        ((g⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *
        (By : Matrix (Fin n) (Fin n) D.host.E)) a b) ∈ bwA_Ow D w := by
    intro a b
    obtain ⟨s, hs, hsY⟩ := hcol Y By hBy b
    obtain ⟨t, ht, htm⟩ : ∃ t ∈ (A.Pv v).primeCompl, t • ((s : D.host.E) •
        ((By : Matrix (Fin n) (Fin n) D.host.E) *ᵥ Pi.single b 1)) ∈
        mulLat (g : Matrix (Fin n) (Fin n) D.host.E) X := h1 hsY
    obtain ⟨x', hx', hgx⟩ := Submodule.mem_map.mp htm
    have hgx' : (g : Matrix (Fin n) (Fin n) D.host.E) *ᵥ x' = t • ((s : D.host.E) •
        ((By : Matrix (Fin n) (Fin n) D.host.E) *ᵥ Pi.single b 1)) := hgx
    have hx'eq : x' = (t * (s : 𝓞 D.host.E)) •
        (((g⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *ᵥ
          ((By : Matrix (Fin n) (Fin n) D.host.E) *ᵥ Pi.single b 1)) := by
      calc x' = ((g⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *ᵥ
            ((g : Matrix (Fin n) (Fin n) D.host.E) *ᵥ x') := by
              rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
        _ = _ := by rw [hgx', Matrix.mulVec_smul, Matrix.mulVec_smul, hsmul]
    have hmemX := hx'eq ▸ hx'
    have hc := coord_mem A w hw hseen v hBx _ _ (hprime t s ht hs) hmemX a
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at hc
    exact hc
  have hN' : ∀ a b, embT D ((D.fm u).tauOf w v)
      ((((By⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *
        (g : Matrix (Fin n) (Fin n) D.host.E) *
        (Bx : Matrix (Fin n) (Fin n) D.host.E)) a b) ∈ bwA_Ow D w := by
    intro a b
    obtain ⟨s, hs, hsX⟩ := hcol X Bx hBx b
    have hm : (g : Matrix (Fin n) (Fin n) D.host.E) *ᵥ ((s : D.host.E) •
        ((Bx : Matrix (Fin n) (Fin n) D.host.E) *ᵥ Pi.single b 1)) ∈
        mulLat (g : Matrix (Fin n) (Fin n) D.host.E) X := Submodule.mem_map_of_mem hsX
    obtain ⟨t, ht, htY⟩ : ∃ t ∈ (A.Pv v).primeCompl, t • ((g : Matrix (Fin n) (Fin n) D.host.E) *ᵥ
        ((s : D.host.E) • ((Bx : Matrix (Fin n) (Fin n) D.host.E) *ᵥ Pi.single b 1))) ∈ Y := h2 hm
    have heq : (t * (s : 𝓞 D.host.E)) • ((g : Matrix (Fin n) (Fin n) D.host.E) *ᵥ
        ((Bx : Matrix (Fin n) (Fin n) D.host.E) *ᵥ Pi.single b 1)) =
        t • ((g : Matrix (Fin n) (Fin n) D.host.E) *ᵥ
        ((s : D.host.E) • ((Bx : Matrix (Fin n) (Fin n) D.host.E) *ᵥ Pi.single b 1))) := by
      rw [hsmul, Matrix.mulVec_smul]
    rw [← heq] at htY
    have hc := coord_mem A w hw hseen v hBy _ _ (hprime t s ht hs) htY a
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at hc
    exact hc
  have hprod : ((Bx⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *
      ((g⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *
      (By : Matrix (Fin n) (Fin n) D.host.E) *
      (((By⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *
        (g : Matrix (Fin n) (Fin n) D.host.E) * (Bx : Matrix (Fin n) (Fin n) D.host.E)) = 1 := by
    simp [mul_assoc]
  refine ⟨(((By⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) *
      (g : Matrix (Fin n) (Fin n) D.host.E) * (Bx : Matrix (Fin n) (Fin n) D.host.E)).map
        (embT D ((D.fm u).tauOf w v)), ?_, ?_, ?_⟩
  · show ((Bx⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E).map
        (embT D ((D.fm u).tauOf w v)) *
      ((g⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E).map
        (embT D ((D.fm u).tauOf w v)) *
      (By : Matrix (Fin n) (Fin n) D.host.E).map (embT D ((D.fm u).tauOf w v)) * _ = 1
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, hprod,
      Matrix.map_one _ (map_zero _) (map_one _)]
  · intro a b
    show (((Bx⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E).map
        (embT D ((D.fm u).tauOf w v)) *
      ((g⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E).map
        (embT D ((D.fm u).tauOf w v)) *
      (By : Matrix (Fin n) (Fin n) D.host.E).map (embT D ((D.fm u).tauOf w v))) a b ∈ bwA_Ow D w
    rw [← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]
    exact hN a b
  · intro a b
    exact hN' a b

end PI.UnitaryGroupMassFormula.IAT

end
end

