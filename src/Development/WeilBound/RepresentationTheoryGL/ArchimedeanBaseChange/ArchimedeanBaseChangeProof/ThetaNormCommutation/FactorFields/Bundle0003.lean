module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.IndexNeZeroOfOpenLe
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.Invar2P

theorem index_ne_zero_of_open_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K U : Subgroup G) (hK : IsCompact (K : Set G)) (hU : IsOpen (U : Set G)) (R : Subgroup K)
    (hR : U.subgroupOf K ≤ R) : R.index ≠ 0 := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have : Finite (K ⧸ U.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen K U hU)
  have h0 : (U.subgroupOf K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  intro h
  apply h0
  exact Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_dvd_of_le hR)

end PositivityTheory.Rg.BcB.G3.Invar2P

namespace PositivityTheory.Rg.BcB.G3

theorem invar2_pf : Invar2 := by
  intro E _ _ _ hU a b w K₁ K₂ hK₁ hK₂ φ hφ y g
  obtain ⟨-, -, -, -, hOa, hCa, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hU a w
  obtain ⟨-, -, -, -, hOb, hCb, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hU b w
  refine GlobalTheory.TwOrbConj.twOrb_twConj _ _ _ y g φ fun x => ?_
  refine Invar2P.index_ne_zero_of_open_le ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) (K₁.prod K₂)
    (by rw [Subgroup.coe_prod]; exact hCa.prod hCb) (by rw [Subgroup.coe_prod]; exact hK₁.1.prod hK₂.1) _ ?_
  intro k hk
  rw [Subgroup.mem_subgroupOf] at hk
  rw [GlobalTheory.TwOrbConj.mem_rStab]
  intro u
  have hθk : ((thL a w).prodMap (thL b w)) (k : GLw a w × GLw b w) ∈ K₁.prod K₂ :=
    Subgroup.mem_prod.2 ⟨hK₁.2.2 _ (Subgroup.mem_prod.1 hk).1, hK₂.2.2 _ (Subgroup.mem_prod.1 hk).2⟩
  have e : ((x * ((u * k : _) : GLw a w × GLw b w))⁻¹ * y * ((thL a w).prodMap (thL b w)) (x * ((u * k : _) : GLw a w × GLw b w))) =
      (k : GLw a w × GLw b w)⁻¹ * ((x * (u : GLw a w × GLw b w))⁻¹ * y * ((thL a w).prodMap (thL b w)) (x * (u : GLw a w × GLw b w))) *
        ((thL a w).prodMap (thL b w)) (k : GLw a w × GLw b w) := by
    simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev]; group
  show φ _ = φ _
  rw [e, (hφ.2 _ hθk _).2, (hφ.2 _ ((K₁.prod K₂).inv_mem hk) _).1]

end PositivityTheory.Rg.BcB.G3
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PClsEq
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.ClsEqP

variable {k : Type} [Field k] {n : ℕ} {B : Type} [CommRing B]

def psi (ρ : B →+* Matrix (Fin n) (Fin n) k) (s : k) : B[X] →+* Matrix (Fin n) (Fin n) k :=
  Polynomial.eval₂RingHom' ρ (s • (1 : Matrix (Fin n) (Fin n) k)) (fun a => (Commute.one_right (ρ a)).smul_right s)

theorem psi_C (ρ : B →+* Matrix (Fin n) (Fin n) k) (s : k) (a : B) : psi ρ s (C a) = ρ a :=
  Polynomial.eval₂_C _ _

theorem psi_X (ρ : B →+* Matrix (Fin n) (Fin n) k) (s : k) : psi ρ s X = s • (1 : Matrix (Fin n) (Fin n) k) :=
  Polynomial.eval₂_X _ _

theorem psi_P (ρ : B →+* Matrix (Fin n) (Fin n) k) (s : k) (u v : B) :
    psi ρ s (C u + X * C v) = ρ u + s • ρ v := by
  rw [map_add (f := _), map_mul, psi_C, psi_X, psi_C, Matrix.smul_mul, Matrix.one_mul]

theorem psi_Q (ρ : B →+* Matrix (Fin n) (Fin n) k) (s : k) (u v : B) :
    psi ρ s (C u - X * C v) = ρ u - s • ρ v := by
  rw [map_sub, map_mul, psi_C, psi_X, psi_C, Matrix.smul_mul, Matrix.one_mul]

theorem psi_rel {d : B} {ρ : B →+* Matrix (Fin n) (Fin n) k} {s : k} (hd : ρ d = (s ^ 2) • (1 : Matrix (Fin n) (Fin n) k)) :
    psi ρ s (X ^ 2 - C d) = 0 := by
  rw [map_sub, map_pow, psi_X, psi_C, hd, _root_.smul_pow, one_pow, sub_self]

theorem psi_eq {d : B} {ρ : B →+* Matrix (Fin n) (Fin n) k} {s : k} (hd : ρ d = (s ^ 2) • (1 : Matrix (Fin n) (Fin n) k))
    (F G H : B[X]) (h : F = G + (X ^ 2 - C d) * H) : psi ρ s F = psi ρ s G := by
  rw [h, map_add (f := _), map_mul, psi_rel hd, zero_mul, add_zero]

theorem GA {d : B} {ρ : B →+* Matrix (Fin n) (Fin n) k} {s : k} (hd : ρ d = (s ^ 2) • (1 : Matrix (Fin n) (Fin n) k))
    (u v a : B) : (ρ u + s • ρ v) * ρ a * (ρ u - s • ρ v) = ρ ((u ^ 2 - d * v ^ 2) * a) := by
  rw [← psi_P, ← psi_Q, ← psi_C ρ s a, ← psi_C ρ s ((u ^ 2 - d * v ^ 2) * a), ← map_mul, ← map_mul]
  exact psi_eq hd _ _ (C (- v ^ 2 * a)) (by simp only [map_mul, map_sub, map_pow, map_neg]; ring)

theorem AG {d : B} {ρ : B →+* Matrix (Fin n) (Fin n) k} {s : k} (hd : ρ d = (s ^ 2) • (1 : Matrix (Fin n) (Fin n) k))
    (u v a : B) : (ρ u - s • ρ v) * ρ a * (ρ u + s • ρ v) = ρ ((u ^ 2 - d * v ^ 2) * a) := by
  rw [← psi_P, ← psi_Q, ← psi_C ρ s a, ← psi_C ρ s ((u ^ 2 - d * v ^ 2) * a), ← map_mul, ← map_mul]
  exact psi_eq hd _ _ (C (- v ^ 2 * a)) (by simp only [map_mul, map_sub, map_pow, map_neg]; ring)

theorem A_comm (ρ : B →+* Matrix (Fin n) (Fin n) k) (s : k) (u v a : B) :
    (ρ u - s • ρ v) * ρ a = ρ a * (ρ u - s • ρ v) := by
  rw [← psi_Q, ← psi_C ρ s a, ← map_mul, ← map_mul, mul_comm]

theorem adj_span {c : k →+* k} {δ : GL (Fin n) k} {s : k} {d : B} {ρ : B →+* Matrix (Fin n) (Fin n) k}
    (hF : IsFrame c δ s d ρ) (hcs : c s = -s) (u v : B) :
    δ.val * GlobalTheory.Tw.Phi n k * ((ρ u + s • ρ v).map c)ᵀ = (ρ u - s • ρ v) * (δ.val * GlobalTheory.Tw.Phi n k) := by
  have e : ((ρ u + s • ρ v).map c)ᵀ = ((ρ u).map c)ᵀ + (-s) • ((ρ v).map c)ᵀ := by
    ext i j
    simp [hcs]
  rw [e, Matrix.mul_add, Matrix.mul_smul, ← hF.adj, ← hF.adj, Matrix.sub_mul, Matrix.smul_mul, neg_smul,
    sub_eq_add_neg]

theorem A_delta_theta {c : k →+* k} {δ : GL (Fin n) k} {s : k} {d : B} {ρ : B →+* Matrix (Fin n) (Fin n) k}
    (hF : IsFrame c δ s d ρ) (hcs : c s = -s) (g : GL (Fin n) k) (u v : B) (hg : g.val = ρ u + s • ρ v) :
    (ρ u - s • ρ v) * (δ.val * (thetaGL n c g).val) = δ.val := by
  rw [ClsNormP.thetaGL_val']
  have hXY : (g.val.map c)ᵀ * ((g⁻¹).val.map c)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one c (map_zero c) (map_one c),
      Matrix.transpose_one]
  calc (ρ u - s • ρ v) * (δ.val * (GlobalTheory.Tw.Phi n k * ((g⁻¹).val.map c)ᵀ * (GlobalTheory.Tw.Phi n k)ᵀ))
      = ((ρ u - s • ρ v) * (δ.val * GlobalTheory.Tw.Phi n k)) * ((g⁻¹).val.map c)ᵀ * (GlobalTheory.Tw.Phi n k)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = δ.val * GlobalTheory.Tw.Phi n k * ((g.val.map c)ᵀ * ((g⁻¹).val.map c)ᵀ) * (GlobalTheory.Tw.Phi n k)ᵀ := by
        rw [← adj_span hF hcs u v, ← hg]; simp only [Matrix.mul_assoc]
    _ = δ.val := by
        rw [hXY, Matrix.mul_one, Matrix.mul_assoc, ClsNormP.phi_mul_transpose_eq_one, Matrix.mul_one]

end PositivityTheory.Rg.BcB.G3.ClsEqP

namespace PositivityTheory.Rg.BcB.G3

open ClsEqP in
theorem clsEq_pf : ClsEq := by
  intro k _ _ n c hc δ s hs0 hcs B _ d ρ hF t t'
  constructor
  · rintro ⟨g, hg⟩
    have hN := clsNorm_pf k n c hc δ s hs0 hcs B d ρ hF t
    have hN' := clsNorm_pf k n c hc δ s hs0 hcs B d ρ hF t'
    have e : g⁻¹ * pt δ ρ t * thetaGL n c g * thetaGL n c (g⁻¹ * pt δ ρ t * thetaGL n c g) =
        g⁻¹ * (pt δ ρ t * thetaGL n c (pt δ ρ t)) * g := by
      simp only [map_mul, map_inv, GlobalTheory.LocTwist.thetaGL_thetaGL n c hc]; group
    rw [hg, e, hN] at hN'
    have hcomm : g * (δ * thetaGL n c δ) = (δ * thetaGL n c δ) * g := by
      calc g * (δ * thetaGL n c δ) = g * (g⁻¹ * (δ * thetaGL n c δ) * g) := by rw [hN']
        _ = (δ * thetaGL n c δ) * g := by group
    obtain ⟨u, v, huv⟩ := hF.span g.val (by simpa only [Units.val_mul] using congrArg Units.val hcomm)
    have hA := A_delta_theta hF hcs g u v huv
    have hg1 : g * pt δ ρ t' = pt δ ρ t * thetaGL n c g := by rw [hg]; group
    have hg2 : g.val * (ρ t' * δ.val) = ρ t * δ.val * (thetaGL n c g).val := by
      simpa only [pt, Units.val_mul, ClsNormP.units_map_val] using congrArg Units.val hg1
    have h3 : ρ ((u ^ 2 - d * v ^ 2) * t') * δ.val = ρ t * δ.val := by
      calc ρ ((u ^ 2 - d * v ^ 2) * t') * δ.val = (ρ u - s • ρ v) * ρ 1 * g.val * (ρ t' * δ.val) := by
            rw [huv, AG hF.sq u v 1, mul_one, map_mul, Matrix.mul_assoc]
        _ = (ρ u - s • ρ v) * (ρ t * δ.val * (thetaGL n c g).val) := by
            rw [map_one, Matrix.mul_one, Matrix.mul_assoc, hg2]
        _ = ρ t * ((ρ u - s • ρ v) * (δ.val * (thetaGL n c g).val)) := by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, A_comm, Matrix.mul_assoc, Matrix.mul_assoc]
        _ = ρ t * δ.val := by rw [hA]
    have h4 : ρ ((u ^ 2 - d * v ^ 2) * t') = ρ t := by
      have := congrArg (· * (δ⁻¹).val) h3
      simpa only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] using this
    exact ⟨u, v, by rw [← hF.inj h4, mul_comm]⟩
  · rintro ⟨u, v, huv⟩
    set w : Bˣ := t'⁻¹ * t with hwdef
    have hw : (w : B) = u ^ 2 - d * v ^ 2 := by
      rw [hwdef, Units.val_mul, huv, ← mul_assoc, Units.inv_mul, one_mul]
    have h1 : (ρ u + s • ρ v) * ((ρ u - s • ρ v) * ρ (↑w⁻¹ : B)) = 1 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_one (ρ u + s • ρ v), ← map_one ρ, GA hF.sq u v 1, ← map_mul, ← hw,
        mul_one, Units.mul_inv]
    have h2 : ((ρ u - s • ρ v) * ρ (↑w⁻¹ : B)) * (ρ u + s • ρ v) = 1 := by
      rw [AG hF.sq u v, ← hw, Units.mul_inv, map_one]
    have h5 : (ρ u + s • ρ v) * ρ (↑w⁻¹ : B) * (ρ u - s • ρ v) = 1 := by
      rw [GA hF.sq u v, ← hw, Units.mul_inv, map_one]
    let G : GL (Fin n) k := ⟨ρ u + s • ρ v, (ρ u - s • ρ v) * ρ (↑w⁻¹ : B), h1, h2⟩
    refine ⟨G, ?_⟩
    have hA := A_delta_theta hF hcs G u v rfl
    have hθ : δ.val * (thetaGL n c G).val = (ρ u + s • ρ v) * ρ (↑w⁻¹ : B) * δ.val := by
      calc δ.val * (thetaGL n c G).val
          = (ρ u + s • ρ v) * ρ (↑w⁻¹ : B) * (ρ u - s • ρ v) * (δ.val * (thetaGL n c G).val) := by
            rw [h5, Matrix.one_mul]
        _ = (ρ u + s • ρ v) * ρ (↑w⁻¹ : B) * δ.val := by rw [Matrix.mul_assoc _ (ρ u - s • ρ v), hA]
    have hB : ((w * w⁻¹ * t * w⁻¹ : Bˣ) : B) = t' := by
      congr 1; rw [hwdef]; group
    apply Units.ext
    simp only [pt, Units.val_mul, ClsNormP.units_map_val]
    change ρ t' * δ.val = (ρ u - s • ρ v) * ρ (↑w⁻¹ : B) * (ρ t * δ.val) * (thetaGL n c G).val
    calc ρ (t' : B) * δ.val = ρ ((u ^ 2 - d * v ^ 2) * ((↑w⁻¹ : B) * t) * (↑w⁻¹ : B)) * δ.val := by
          rw [← hw, ← hB]; simp only [Units.val_mul, mul_assoc]
      _ = (ρ u - s • ρ v) * ρ ((↑w⁻¹ : B) * t) * (ρ u + s • ρ v) * ρ (↑w⁻¹ : B) * δ.val := by
          rw [AG hF.sq u v, map_mul]
      _ = (ρ u - s • ρ v) * ρ (↑w⁻¹ : B) * (ρ t * δ.val) * (thetaGL n c G).val := by
          rw [Matrix.mul_assoc _ (ρ t * δ.val), Matrix.mul_assoc (ρ t), hθ, map_mul]
          simp only [Matrix.mul_assoc]

end PositivityTheory.Rg.BcB.G3

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.RelEquiv
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.Count2P

theorem rel_equiv {G : Type} [Group G] (θ : G →* G) :
    Equivalence (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) := by
  constructor
  · exact fun x => ⟨1, by simp⟩
  · rintro x y ⟨g, rfl⟩
    exact ⟨g⁻¹, by rw [map_inv]; group⟩
  · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨g * h, by rw [map_mul]; group⟩

theorem mk_eq_iff {G : Type} [Group G] (θ : G →* G) (x z : G) :
    (Quot.mk (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) x : TwCl θ) = Quot.mk _ z ↔ ∃ g, x = g⁻¹ * z * θ g := by
  constructor
  · intro h
    exact (rel_equiv θ).symm ((rel_equiv θ).eqvGen_iff.1 (Quot.eqvGen_exact h))
  · intro h
    exact (Quot.sound ((rel_equiv θ).symm h))

theorem prod_rel {G H : Type} [Group G] [Group H] (θ₁ : G →* G) (θ₂ : H →* H) (x z : G × H) :
    (∃ g : G × H, x = g⁻¹ * z * (θ₁.prodMap θ₂) g) ↔
      (∃ g₁, x.1 = g₁⁻¹ * z.1 * θ₁ g₁) ∧ (∃ g₂, x.2 = g₂⁻¹ * z.2 * θ₂ g₂) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨⟨g.1, rfl⟩, ⟨g.2, rfl⟩⟩
  · rintro ⟨⟨g₁, h₁⟩, ⟨g₂, h₂⟩⟩
    exact ⟨(g₁, g₂), Prod.ext h₁ h₂⟩

theorem charpoly_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E)
    (x z : GLw n w) (h : ∃ g, x = g⁻¹ * z * thL n w g) :
    (nrmL n w x).val.charpoly = (nrmL n w z).val.charpoly := by
  obtain ⟨g, rfl⟩ := h
  have h1 : nrmL n w (g⁻¹ * z * thL n w g) = g⁻¹ * nrmL n w z * g := GlobalTheory.BCT.ThBasic.nrmL_twist hU n w g z
  have h2 : ((g⁻¹ * nrmL n w z * g : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      ((g⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * (nrmL n w z : Matrix (Fin n) (Fin n) _) *
        (g : Matrix (Fin n) (Fin n) _) := rfl
  rw [h1, h2, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj' g _

end PositivityTheory.Rg.BcB.G3.Count2P

open PositivityTheory.Rg.BcB.G3.Count2P in
theorem PositivityTheory.Rg.BcB.G3.count2_pf (h1 : Count1) : Count2 := by
  intro E _ _ _ hU a b S hS P₁ hP₁ P₂ hP₂ y hy hint
  obtain ⟨zz, hzz, hzK⟩ : ∃ zz : ∀ w : Pl E, GLw a w × GLw b w,
      (∀ w, (Quot.mk _ (zz w) : TwCl ((thL a w).prodMap (thL b w))) = y w) ∧
        ∀ᶠ w in cofinite, zz w ∈ (GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)) := by
    refine ⟨fun w => if h : ∃ z ∈ ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))),
        y w = Quot.mk _ z then h.choose else (y w).rep, fun w => ?_, hint.mono fun w hw => ?_⟩
    · dsimp only
      split_ifs with h
      · exact h.choose_spec.2.symm
      · exact Quot.out_eq _
    · dsimp only
      rw [dite_eq_left hw]
      exact hw.choose_spec.1
  have hrel : ∀ w, ∃ g, (y w).rep = g⁻¹ * zz w * ((thL a w).prodMap (thL b w)) g := by
    intro w
    rw [← mk_eq_iff, hzz w]
    exact Quot.out_eq _
  have hc1 : ∀ w, (nrmL a w (zz w).1).val.charpoly = atPl w P₁ := fun w => by
    rw [← (hy w).1]
    exact (charpoly_eq hU a w _ _ ((prod_rel _ _ _ _).1 (hrel w)).1).symm
  have hc2 : ∀ w, (nrmL b w (zz w).2).val.charpoly = atPl w P₂ := fun w => by
    rw [← (hy w).2]
    exact (charpoly_eq hU b w _ _ ((prod_rel _ _ _ _).1 (hrel w)).2).symm
  have e1 : Nat.card {c : TwCl (thE E a) // (c.rep * thE E a c.rep).val.charpoly = P₁ ∧
      ∀ w ∈ S, ∃ g, locEl a w c.rep = g⁻¹ * (zz w).1 * thL a w g} * 2 ^ nfac P₁ =
      2 ^ (a * Fintype.card (InfinitePlace E)) :=
    h1 E hU a S hS P₁ hP₁ (fun w => (zz w).1) hc1 (hzK.mono fun w hw => (Subgroup.mem_prod.1 hw).1)
  have e2 : Nat.card {c : TwCl (thE E b) // (c.rep * thE E b c.rep).val.charpoly = P₂ ∧
      ∀ w ∈ S, ∃ g, locEl b w c.rep = g⁻¹ * (zz w).2 * thL b w g} * 2 ^ nfac P₂ =
      2 ^ (b * Fintype.card (InfinitePlace E)) :=
    h1 E hU b S hS P₂ hP₂ (fun w => (zz w).2) hc2 (hzK.mono fun w hw => (Subgroup.mem_prod.1 hw).2)
  have key : ∀ (c : TwCl (thE E a) × TwCl (thE E b)) (w : Pl E),
      (Quot.mk _ (locEl a w c.1.rep, locEl b w c.2.rep) : TwCl ((thL a w).prodMap (thL b w))) = y w ↔
        (∃ g, locEl a w c.1.rep = g⁻¹ * (zz w).1 * thL a w g) ∧
          (∃ g, locEl b w c.2.rep = g⁻¹ * (zz w).2 * thL b w g) := by
    intro c w
    rw [← hzz w]
    exact (mk_eq_iff _ _ _).trans (prod_rel _ _ _ _)
  let eqv : {c : TwCl (thE E a) × TwCl (thE E b) // ((c.1.rep * thE E a c.1.rep).val.charpoly = P₁ ∧
      (c.2.rep * thE E b c.2.rep).val.charpoly = P₂) ∧ ∀ w ∈ S,
      (Quot.mk _ (locEl a w c.1.rep, locEl b w c.2.rep) : TwCl ((thL a w).prodMap (thL b w))) = y w} ≃
      {c : TwCl (thE E a) // (c.rep * thE E a c.rep).val.charpoly = P₁ ∧
        ∀ w ∈ S, ∃ g, locEl a w c.rep = g⁻¹ * (zz w).1 * thL a w g} ×
      {c : TwCl (thE E b) // (c.rep * thE E b c.rep).val.charpoly = P₂ ∧
        ∀ w ∈ S, ∃ g, locEl b w c.rep = g⁻¹ * (zz w).2 * thL b w g} :=
    { toFun := fun c => (⟨c.1.1, c.2.1.1, fun w hw => ((key c.1 w).1 (c.2.2 w hw)).1⟩,
        ⟨c.1.2, c.2.1.2, fun w hw => ((key c.1 w).1 (c.2.2 w hw)).2⟩)
      invFun := fun p => ⟨(p.1.1, p.2.1), ⟨p.1.2.1, p.2.2.1⟩,
        fun w hw => (key (p.1.1, p.2.1) w).2 ⟨p.1.2.2 w hw, p.2.2.2 w hw⟩⟩
      left_inv := fun c => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr eqv, Nat.card_prod, add_mul, pow_add, pow_add, ← e1, ← e2]
  ring

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TwConjOfMkEq
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.FinCl2P

theorem rel_of_eqvGen {G : Type} [Group G] (θ : G →* G) {x y : G}
    (h : Relation.EqvGen (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) x y) : ∃ g, y = g⁻¹ * x * θ g := by
  induction h with
  | rel a b hab => exact hab
  | refl a => exact ⟨1, by simp⟩
  | symm a b _ ih =>
    obtain ⟨g, rfl⟩ := ih
    exact ⟨g⁻¹, by rw [map_inv]; group⟩
  | trans a b c _ _ ih1 ih2 =>
    obtain ⟨g, rfl⟩ := ih1
    obtain ⟨k, rfl⟩ := ih2
    exact ⟨g * k, by rw [map_mul]; group⟩

theorem twConj_of_mk_eq {G : Type} [Group G] {θ : G →* G} {x y : G}
    (h : (Quot.mk _ x : TwCl θ) = Quot.mk _ y) : ∃ g, y = g⁻¹ * x * θ g :=
  rel_of_eqvGen θ (Quot.eqvGen_exact h)

theorem rep_mk {G : Type} [Group G] {θ : G →* G} (y : G) :
    ∃ g, TwCl.rep (Quot.mk _ y : TwCl θ) = g⁻¹ * y * θ g :=
  twConj_of_mk_eq (θ := θ) (Quot.out_eq (Quot.mk _ y : TwCl θ)).symm

theorem charpoly_rep_mk {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E)
    (y : GLw n w) : (nrmL n w (TwCl.rep (Quot.mk _ y : TwCl (thL n w)))).val.charpoly = (nrmL n w y).val.charpoly := by
  obtain ⟨g, hg⟩ := rep_mk (θ := thL n w) y
  rw [hg, GlobalTheory.BCT.ThBasic.nrmL_twist hU n w g y, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
    Matrix.charpoly_units_conj']

end PositivityTheory.Rg.BcB.G3.FinCl2P

open PositivityTheory.Rg.BcB.G3.FinCl2P in
theorem PositivityTheory.Rg.BcB.G3.finCl2_pf : FinCl2 := by
  intro E _ _ _ hU a b w Q₁ Q₂ h₁ h₂
  set θ := (thL a w).prodMap (thL b w) with hθ
  let f : TwCl θ → TwCl (thL a w) × TwCl (thL b w) := fun l => (Quot.mk _ l.rep.1, Quot.mk _ l.rep.2)
  have hinj : Function.Injective f := by
    intro l l' hll'
    obtain ⟨g₁, hg₁⟩ := twConj_of_mk_eq (congrArg Prod.fst hll')
    obtain ⟨g₂, hg₂⟩ := twConj_of_mk_eq (congrArg Prod.snd hll')
    have hq : (Quot.mk _ l.rep : TwCl θ) = Quot.mk _ l'.rep :=
      Quot.sound ⟨(g₁, g₂), Prod.ext (by simpa [hθ] using hg₁) (by simpa [hθ] using hg₂)⟩
    have e1 : (Quot.mk _ l.rep : TwCl θ) = l := Quot.out_eq l
    have e2 : (Quot.mk _ l'.rep : TwCl θ) = l' := Quot.out_eq l'
    rw [← e1, ← e2, hq]
  have hA := (GlobalTheory.BCT.ClsFin.classes_finite E hU a w Q₁ h₁).1
  have hB := (GlobalTheory.BCT.ClsFin.classes_finite E hU b w Q₂ h₂).1
  refine ((hA.prod hB).preimage hinj.injOn).subset ?_
  rintro l ⟨hl₁, hl₂⟩
  refine ⟨?_, ?_⟩
  · change (nrmL a w (TwCl.rep (Quot.mk _ l.rep.1 : TwCl (thL a w)))).val.charpoly = Q₁
    rw [charpoly_rep_mk hU a w, hl₁]
  · change (nrmL b w (TwCl.rep (Quot.mk _ l.rep.2 : TwCl (thL b w)))).val.charpoly = Q₂
    rw [charpoly_rep_mk hU b w, hl₂]
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.UnitPairOfSupport
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.Unit2P

theorem isCompact_fst {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H] [T2Space G]
    (t : G × H) (h : IsCompact (closure (Subgroup.zpowers t : Set (G × H)))) :
    IsCompact (closure (Subgroup.zpowers t.1 : Set G)) := by
  have hc : IsCompact (Prod.fst '' closure (Subgroup.zpowers t : Set (G × H))) := h.image continuous_fst
  have hs : (Subgroup.zpowers t.1 : Set G) ⊆ Prod.fst '' closure (Subgroup.zpowers t : Set (G × H)) := by
    rintro x ⟨k, rfl⟩
    exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩
  exact hc.of_isClosed_subset isClosed_closure (closure_minimal hs hc.isClosed)

theorem isCompact_snd {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H] [T2Space H]
    (t : G × H) (h : IsCompact (closure (Subgroup.zpowers t : Set (G × H)))) :
    IsCompact (closure (Subgroup.zpowers t.2 : Set H)) := by
  have hc : IsCompact (Prod.snd '' closure (Subgroup.zpowers t : Set (G × H))) := h.image continuous_snd
  have hs : (Subgroup.zpowers t.2 : Set H) ⊆ Prod.snd '' closure (Subgroup.zpowers t : Set (G × H)) := by
    rintro x ⟨k, rfl⟩
    exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩
  exact hc.of_isClosed_subset isClosed_closure (closure_minimal hs hc.isClosed)

end PositivityTheory.Rg.BcB.G3.Unit2P

namespace PositivityTheory.Rg.BcB.G3

theorem unit_pair_of_support (h1 : LocGood) (h2 : GenUnit) (h3 : Supp) : Unit2 := by
  intro E _ _ _ hU a b P₁ hP₁ P₂ hP₂
  filter_upwards [h1 E hU a P₁ hP₁, h1 E hU b P₂ hP₂] with w hw1 hw2
  intro y z hy1 hy2 hz1 hz2 hzK
  obtain ⟨hA1, hB1, hC1⟩ := hw1 z.1 (Subgroup.mem_prod.1 hzK).1 hz1
  obtain ⟨hA2, hB2, hC2⟩ := hw2 z.2 (Subgroup.mem_prod.1 hzK).2 hz2
  set K := (GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)) with hK
  set θ := (thL a w).prodMap (thL b w) with hθ
  have hnt : ∀ (m : ℕ) (g y : GLw m w),
      (nrmL m w (g⁻¹ * y * thL m w g)).val.charpoly = (nrmL m w y).val.charpoly := by
    intro m g y
    rw [ThBasic.nrmL_twist hU, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']
  have hconjK : ∀ y' ∈ K, (nrmL a w y'.1).val.charpoly = atPl w P₁ → (nrmL b w y'.2).val.charpoly = atPl w P₂ →
      ∃ g, y' = g⁻¹ * z * θ g := by
    intro y' hy' e1 e2
    obtain ⟨g1, hg1⟩ := hC1 y'.1 (Subgroup.mem_prod.1 hy').1 e1
    obtain ⟨g2, hg2⟩ := hC2 y'.2 (Subgroup.mem_prod.1 hy').2 e2
    exact ⟨(g1, g2), Prod.ext hg1 hg2⟩
  refine ⟨?_, fun hyK => hconjK y hyK hy1 hy2⟩
  by_cases hex : ∃ g, y = g⁻¹ * z * θ g
  · rw [if_pos hex]
    obtain ⟨g, rfl⟩ := hex
    refine h2 _ θ K z ?_ hzK ?_ ?_ g
    · intro k hk
      exact Subgroup.mem_prod.2 ⟨ThBasic.thL_mem_KGL hU a w _ (Subgroup.mem_prod.1 hk).1,
        ThBasic.thL_mem_KGL hU b w _ (Subgroup.mem_prod.1 hk).2⟩
    · intro g hg
      obtain ⟨t1, ht1, k1, hk1, e1⟩ := hA1 g.1 (Subgroup.mem_prod.1 hg).1
      obtain ⟨t2, ht2, k2, hk2, e2⟩ := hA2 g.2 (Subgroup.mem_prod.1 hg).2
      refine ⟨(t1, t2), ?_, (k1, k2), Subgroup.mem_prod.2 ⟨hk1, hk2⟩, Prod.ext e1 e2⟩
      have ht1' : t1 * z.1 = z.1 * thL a w t1 := ht1
      have ht2' : t2 * z.2 = z.2 * thL b w t2 := ht2
      show (t1, t2) * z = z * θ (t1, t2)
      exact Prod.ext ht1' ht2'
    · intro t ht hc
      have ht' : t * z = z * θ t := ht
      have e1 : t.1 * z.1 = z.1 * thL a w t.1 := congrArg Prod.fst ht'
      have e2 : t.2 * z.2 = z.2 * thL b w t.2 := congrArg Prod.snd ht'
      exact Subgroup.mem_prod.2 ⟨hB1 t.1 e1 (Unit2P.isCompact_fst t hc), hB2 t.2 e2 (Unit2P.isCompact_snd t hc)⟩
  · rw [if_neg hex]
    by_contra hne
    obtain ⟨g, hg⟩ := h3 _ θ K y _ hne
    have hmem : g⁻¹ * y * θ g ∈ K := by
      by_contra hm
      exact hg (Set.indicator_of_notMem (show g⁻¹ * y * θ g ∉ (K : Set (GLw a w × GLw b w)) from hm) _)
    have c1 : (nrmL a w (g⁻¹ * y * θ g).1).val.charpoly = atPl w P₁ := by
      show (nrmL a w (g.1⁻¹ * y.1 * thL a w g.1)).val.charpoly = _
      rw [hnt]; exact hy1
    have c2 : (nrmL b w (g⁻¹ * y * θ g).2).val.charpoly = atPl w P₂ := by
      show (nrmL b w (g.2⁻¹ * y.2 * thL b w g.2)).val.charpoly = _
      rw [hnt]; exact hy2
    obtain ⟨h, hh⟩ := hconjK _ hmem c1 c2
    apply hex
    refine ⟨h * g⁻¹, ?_⟩
    calc y = g * (g⁻¹ * y * θ g) * (θ g)⁻¹ := by group
      _ = g * (h⁻¹ * z * θ h) * (θ g)⁻¹ := by rw [hh]
      _ = (h * g⁻¹)⁻¹ * z * θ (h * g⁻¹) := by rw [map_mul, map_inv]; group

end PositivityTheory.Rg.BcB.G3

end
end

