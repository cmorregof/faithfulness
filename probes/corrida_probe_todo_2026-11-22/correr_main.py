"""Ejecuta probe.main() entero para Qwen3-4B, sin modificar probe.py.

main() se llama con su carpeta y su parquet por defecto. Solo se pasan dos argumentos que
main() ya admite: la ruta de salida, para que el informe y las figuras queden en esta carpeta
de corrida, y parquet_en_orden=True, porque el parquet no trae columna idx (el 21 nov se
comprobó que sus 500 filas coinciden en orden con el manifiesto en id, source y tag).
"""
import hashlib, sys, time
from datetime import date
from pathlib import Path

AQUI = Path(__file__).resolve().parent
R = AQUI.parent
sys.path.insert(0, str(R))
import probe  # noqa: E402

SHA = hashlib.sha256((R / "probe.py").read_bytes()).hexdigest()
if SHA != "bbdb16350b88494e7c1c6a0d5c51b3003ea41d690327378fb58f06dc697dc30f":
    raise SystemExit(f"probe.py no tiene el SHA esperado: {SHA}")

destino = AQUI / "main_qwen3_4b"
destino.mkdir(exist_ok=True)
t0 = time.perf_counter()
probe.main(salida=destino / f"resultados_{date.today().isoformat()}.md", parquet_en_orden=True)
print(f"main() entero: {time.perf_counter() - t0:.0f} s; probe.py {SHA}")
