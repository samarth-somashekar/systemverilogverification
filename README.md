# FIFO Formal Verification using SystemVerilog Assertions

This project demonstrates the use of **SystemVerilog Assertions (SVA)** to formally verify a simple **synchronous FIFO (First-In First-Out)** module. The verification is simulation-based and was run using **EDA Playground** with **Riviera-PRO**.

---

## 📌 Features

- Parameterized FIFO design (depth and width)
- Verifies:
  - ❌ No writes when FIFO is full
  - ❌ No reads when FIFO is empty
- Assertions written using SVA
- Simulation done online using EDA Playground

---

## 🧠 Concepts Used

- SystemVerilog RTL design
- Assertion-Based Verification (ABV)
- Simulation-based formal-like checking
- FIFO status tracking: `full`, `empty`

---

## 🧾 Files

| File         | Description                                    |
|--------------|------------------------------------------------|
| `fifo.sv`    | RTL code for the synchronous FIFO              |
| `fifo_tb.sv` | Testbench with stimulus and assertions         |
| `eda_playground_link.txt` | Link to run this project online in EDA Playground |

## 🔗 Online Simulation

📎 https://edaplayground.com/x/HfS_
