# ==========================================
# ATOM S3 + ATOM CAN Base
# Ver 8.1 - PIN Authentication + BUS Status
# ==========================================
# 【Ver 8.1 追加機能】
# ★ PIN認証: 4桁PINコードによるBLE接続制限
#   - 初回接続時にPINを設定 → NVSに保存
#   - 以降はWebアプリが自動送信 → 即接続
#   - 誤ったPINは2秒後に切断
#   - SaveデータにPIN含む → ブラウザ初期化後も復元可
#
# ★ CANバス接続検出: フレーム受信で判定
#   - BUS:OK  (緑) → CANフレーム受信中
#   - BUS:--  (灰) → 信号線未接続
#   - CAN:ERR (赤) → コントローラーエラー
#
# ★ PIN表示 (ディスプレイ4行目)
#   PIN:--- → PIN未設定
#   PIN:LOCK → 設定済み・未認証
#   PIN:AUTH → 認証済み・通常動作
#
# 【Ver 8.0 既存機能】
# SET_SLOT_MODEコマンド受信処理
# (LE/BE等のスロットモード設定変更)
#
# 【boot.py を一緒に書き込む】
#   起動高速化のため boot.py でWiFiを無効化する:
#   --- boot.py ---
#   import network
#   network.WLAN(network.STA_IF).active(False)
#   network.WLAN(network.AP_IF).active(False)
#   ---------------
# ==========================================
import M5
from M5 import *
import time
from hardware import I2C, Pin
from machine import mem32
from unit import CANUnit
import bluetooth
import struct
from micropython import const
from esp32 import NVS

TX_PIN       = 6
RX_PIN       = 5
CAN_BAUDRATE = 1000000
CAN_GROUP_1_ID = 0x4E0
CAN_GROUP_2_ID = 0x4E1
can_tx_id    = 0x5A0
k_meter_id   = 0x661
gps_base_id  = 0x400
slot_modes   = [1] * 7
can_state    = bytearray(8)

DRAIN_MAX     = 10
CAN_SEND_INT  = 100
TEMP_SEND_INT = 200
DISP_INT      = 250
VALS_SEND_INT = 20

can             = None
ble_tx_queue    = []
last_vals       = {}
last_vals_send  = 0
allowed_ids_set = set()
last_can_send       = 0
last_temp_send      = 0
last_display        = 0
last_recovery_check = 0
kmeter_found  = False
last_temp_val = 0
can_error     = False
filter_ok     = False
can_rx_count  = 0
can_bus_active = False
nvs           = None
_pending_config_send = False
ble_rx_queue  = []

# ★ GPS to CAN (ADU-5 / ECUMASTER GPStoCAN互換フォーマット)
GPS_SEND_INT   = 300
gps_lat = gps_lon = gps_spd = gps_hdg = gps_alt = 0.0
gps_acc        = 999
last_gps_update = 0
last_gps_send   = 0

# ★ PIN認証 (Ver 8.1)
pin_code         = None     # 設定済みPIN (4桁文字列) or None
pin_verified     = set()    # PIN認証済みのconn_handle
PIN_TIMEOUT      = 10000    # 接続後10秒以内にPIN送信しないと切断

UART_UUID = bluetooth.UUID("6e400001-b5a3-f393-e0a9-e50e24dcca9e")
UART_TX   = bluetooth.UUID("6e400003-b5a3-f393-e0a9-e50e24dcca9e")
UART_RX   = bluetooth.UUID("6e400002-b5a3-f393-e0a9-e50e24dcca9e")
_IRQ_CENTRAL_CONNECT    = const(1)
_IRQ_CENTRAL_DISCONNECT = const(2)
_IRQ_GATTS_WRITE        = const(3)

class BLEUART:
    def __init__(self, ble):
        self._ble = ble
        self._ble.active(True)
        try: self._ble.config(mtu=256)  # ★ デフォルト23byteだとGPSコマンドが切り詰められるため拡張
        except: pass
        self._ble.irq(self._irq)
        ((self._tx, self._rx),) = self._ble.gatts_register_services([
            (UART_UUID, ((UART_TX, bluetooth.FLAG_NOTIFY),
                         (UART_RX, bluetooth.FLAG_WRITE)))
        ])
        self._connections = set()
        self._advertise()

    def _advertise(self):
        try:
            self._ble.gap_advertise(100000, b'\x02\x01\x06\x12\x09M5AtomS3_CAN_Base')
        except: pass

    def _irq(self, event, data):
        global _pending_config_send
        if event == _IRQ_CENTRAL_CONNECT:
            conn_handle = data[0]
            self._connections.add(conn_handle)
            # ★ PIN認証: 接続をキューに積んでメインループで処理
            ble_rx_queue.append("__CONNECT__:%d" % conn_handle)
            _pending_config_send = True
        elif event == _IRQ_CENTRAL_DISCONNECT:
            h = data[0]
            self._connections.discard(h)
            pin_verified.discard(h)   # ★ 切断時に認証状態をクリア
            self._advertise()
        elif event == _IRQ_GATTS_WRITE:
            try:
                cmd = self._ble.gatts_read(self._rx).decode().strip()
                if cmd: ble_rx_queue.append(cmd)
            except: pass

    def send(self, data):
        for conn in self._connections:
            try: self._ble.gatts_notify(conn, self._tx, data)
            except: pass

# ==========================================
# ★ PIN Authentication Functions (Ver 8.1)
# ==========================================
def _set_pin(new_pin):
    global pin_code
    pin_code = new_pin
    if nvs:
        try:
            nvs.set_blob("pin_code", new_pin.encode())
            nvs.commit()
        except: pass
    M5.Display.setCursor(0, 60)
    M5.Display.setTextColor(0x07E0, 0x0000)  # 緑
    M5.Display.print("PIN:SET ")
    print("[PIN] Set:", new_pin)

def _clear_pin():
    global pin_code
    pin_code = None
    if nvs:
        try:
            nvs.set_blob("pin_code", b"")
            nvs.commit()
        except: pass
    M5.Display.fillRect(0, 60, 128, 20, 0x0000)
    print("[PIN] Cleared")

def _load_pin():
    global pin_code
    if not nvs: return
    try:
        buf = bytearray(4)
        nvs.get_blob("pin_code", buf)
        s = buf.decode().strip()
        if len(s) == 4 and s.isdigit():
            pin_code = s
            print("[PIN] Loaded:", pin_code)
    except: pass

def update_hw_filter():
    global allowed_ids_set, filter_ok, can_error
    allowed_ids_set = {CAN_GROUP_1_ID, CAN_GROUP_2_ID}
    if not can: return
    id1 = CAN_GROUP_1_ID & 0x7FF
    id2 = CAN_GROUP_2_ID & 0x7FF
    diff    = (id1 ^ id2) & 0x7FF
    code_id = id1 & (~diff) & 0x7FF
    mask_id = diff
    code_b0 = (code_id >> 3) & 0xFF
    code_b1 = ((code_id & 0x07) << 5) & 0xFF
    mask_b0 = (mask_id >> 3) & 0xFF
    mask_b1 = ((mask_id & 0x07) << 5) | 0x1F
    TWAI_BASE = 0x6002B000
    try:
        mem32[TWAI_BASE + 0x000] = (mem32[TWAI_BASE + 0x000] & 0xFF) | 0x01
        mem32[TWAI_BASE + 0x000] = (mem32[TWAI_BASE + 0x000] & 0xFF) | 0x09
        mem32[TWAI_BASE + 0x040] = code_b0
        mem32[TWAI_BASE + 0x044] = code_b1
        mem32[TWAI_BASE + 0x048] = 0x00
        mem32[TWAI_BASE + 0x04C] = 0x00
        mem32[TWAI_BASE + 0x050] = mask_b0
        mem32[TWAI_BASE + 0x054] = mask_b1
        mem32[TWAI_BASE + 0x058] = 0xFF
        mem32[TWAI_BASE + 0x05C] = 0xFF
        mem32[TWAI_BASE + 0x000] = (mem32[TWAI_BASE + 0x000] & 0xFF) & 0xFE
        time.sleep_ms(10)
        rb = mem32[TWAI_BASE + 0x040] & 0xFF
        filter_ok = (rb == code_b0)
        can_error = False
        print(f"[Filter] ACR0={hex(code_b0)} rb={hex(rb)} {'OK' if filter_ok else 'NG'}")
    except Exception as e:
        filter_ok = False
        print(f"[Filter] FAIL: {e}")

def check_can_recovery():
    global can, last_recovery_check, can_error, can_rx_count, can_bus_active
    now = time.ticks_ms()
    if time.ticks_diff(now, last_recovery_check) < 5000: return
    last_recovery_check = now
    if can_rx_count == 0:
        can_bus_active = False
    can_rx_count = 0
    try:
        if can and can.state() != CANUnit.RUNNING:
            can_error = True
            can.deinit()
            time.sleep_ms(50)
            can = CANUnit(0, port=(TX_PIN, RX_PIN), mode=CANUnit.NORMAL, baudrate=CAN_BAUDRATE)
            time.sleep_ms(100)
            update_hw_filter()
            can_error = False
    except: pass

def queue_config_sync():
    ble_tx_queue.append(("STATE=" + ",".join(str(b) for b in can_state)).encode())
    ble_tx_queue.append(f"GRP1={hex(CAN_GROUP_1_ID)}".encode())
    ble_tx_queue.append(f"GRP2={hex(CAN_GROUP_2_ID)}".encode())
    ble_tx_queue.append(f"ID={hex(can_tx_id)}".encode())
    ble_tx_queue.append(f"KID={hex(k_meter_id)}".encode())
    ble_tx_queue.append(f"GID={hex(gps_base_id)}".encode())

def extract_val(data, pos, mode):
    if len(data) <= pos: return None
    if mode == 0: return data[pos]
    if len(data) <= pos + 1: return None
    if mode == 1: return data[pos] | (data[pos + 1] << 8)
    return (data[pos] << 8) | data[pos + 1]

def safe_can_send(id, data):
    global can_error
    if can:
        try:
            can.send(data, id, timeout=0)
            can_error = False
        except:
            can_error = True

def send_gps_can():
    lat_raw = int(gps_lat * 10000000)
    lon_raw = int(gps_lon * 10000000)
    safe_can_send(gps_base_id, struct.pack('>ii', lat_raw, lon_raw))

    spd_raw = int(gps_spd * 3.6 * 1000 / 36)
    alt_raw = int(gps_alt)
    status = 4 if gps_acc < 30 else 1
    byte7 = (status & 0x07) | ((4 & 0x07) << 3)
    safe_can_send(gps_base_id + 1, struct.pack('>hhBBBB', spd_raw, alt_raw, 0, 0, 0, byte7))

    hdg_raw = int(gps_hdg)
    safe_can_send(gps_base_id + 2, struct.pack('>HHhh', hdg_raw, hdg_raw, 0, 0))

    safe_can_send(gps_base_id + 3, struct.pack('>hhhh', 0, 0, 0, 0))

def process_ble_cmd():
    global CAN_GROUP_1_ID, CAN_GROUP_2_ID, can_tx_id, k_meter_id
    global gps_lat, gps_lon, gps_spd, gps_hdg, gps_alt, gps_acc, last_gps_update
    global gps_base_id
    if not ble_rx_queue: return
    cmd = ble_rx_queue.pop(0)
    try:
        # ★ 接続イベント処理
        if cmd.startswith("__CONNECT__:"):
            conn_handle = int(cmd.split(":")[1])
            if pin_code is None:
                # ★ PIN未設定: 接続を即許可 + 設定を促す通知のみ
                pin_verified.add(conn_handle)
                ble_tx_queue.append(b"NEED_SET_PIN")
            else:
                # PIN設定済み: PIN要求（この間は他コマンドをガード）
                ble_tx_queue.append(b"NEED_PIN")
            return

        # ★ PIN設定コマンド (初回)
        if cmd.startswith("SET_PIN="):
            new_pin = cmd.split("=")[1].strip()
            if len(new_pin) == 4 and new_pin.isdigit():
                _set_pin(new_pin)
                for h in uart._connections:
                    pin_verified.add(h)
                ble_tx_queue.append(b"PIN_OK")
            else:
                ble_tx_queue.append(b"PIN_ERR=invalid")
            return

        # ★ PIN送信コマンド
        if cmd.startswith("PIN="):
            entered = cmd.split("=")[1].strip()
            if pin_code and entered == pin_code:
                for h in uart._connections:
                    pin_verified.add(h)
                ble_tx_queue.append(b"PIN_OK")
            else:
                ble_tx_queue.append(b"PIN_NG")
                time.sleep_ms(2000)
                try:
                    for h in list(uart._connections):
                        uart._ble.gap_disconnect(h)
                except: pass
            return

        # ★ PIN未認証ガード（PIN設定済みの場合のみ）
        # REQUEST_STATE と CLEAR_PIN は認証前でも通す
        if pin_code is not None and cmd not in ("REQUEST_STATE", "CLEAR_PIN"):
            auth_ok = any(h in pin_verified for h in uart._connections)
            if not auth_ok:
                return

        if cmd == "REQUEST_STATE":
            queue_config_sync()
            return

        if cmd.startswith("CFGBTN="):
            p = cmd.split('=')[1].split(',')
            idx = int(p[0])
            on_val = int(p[1])
            off_val = int(p[2])
            if 0 <= idx < 8:
                if nvs:
                    nvs.set_i32(f"btn_off_{idx}", off_val)
                    nvs.commit()
                # 現在がONでなければ(OFFなら)更新
                if can_state[idx] != on_val:
                    can_state[idx] = off_val
                    safe_can_send(can_tx_id, can_state)

        # ★追加: スロットモード(Endian/Byte長)の設定反映
        elif cmd.startswith("SET_SLOT_MODE="):
            p = cmd.split('=')[1].split(',')
            slot_idx = int(p[0])
            mode_val = int(p[1])
            if 0 <= slot_idx < 7:
                slot_modes[slot_idx] = mode_val
                if nvs:
                    nvs.set_i32(f"slot{slot_idx}_mode", mode_val)
                    nvs.commit()
                ble_tx_queue.append(f"SLOT_MODE_OK={slot_idx},{mode_val}".encode())

        elif cmd.startswith("SET_GROUPS="):
            p = cmd.split('=')[1].split(',')
            CAN_GROUP_1_ID = int(p[0], 16)
            CAN_GROUP_2_ID = int(p[1], 16)
            if nvs:
                nvs.set_i32("grp1_id", CAN_GROUP_1_ID)
                nvs.set_i32("grp2_id", CAN_GROUP_2_ID)
                nvs.commit()
            update_hw_filter()
            queue_config_sync()
        elif cmd.startswith("ID="):
            can_tx_id = int(cmd.split('=')[1], 16)
            if nvs: nvs.set_i32("my_id", can_tx_id); nvs.commit()
            ble_tx_queue.append(f"ID={hex(can_tx_id)}".encode())
        elif cmd.startswith("KID="):
            k_meter_id = int(cmd.split('=')[1], 16)
            if nvs: nvs.set_i32("k_meter_id", k_meter_id); nvs.commit()
            ble_tx_queue.append(f"KID={hex(k_meter_id)}".encode())
        elif cmd.startswith("GID="):
            gps_base_id = int(cmd.split('=')[1], 16)
            if nvs: nvs.set_i32("gps_base_id", gps_base_id); nvs.commit()
            ble_tx_queue.append(f"GID={hex(gps_base_id)}".encode())
        elif cmd == "CLEAR_PIN":
            # PIN削除(リセット)
            _clear_pin()
            for h in list(uart._connections):
                pin_verified.discard(h)
            ble_tx_queue.append(b"PIN_CLEARED")

        elif cmd.startswith("A="):
            gps_lat = float(cmd[2:])
            last_gps_update = time.ticks_ms()

        elif cmd.startswith("O="):
            gps_lon = float(cmd[2:])
            last_gps_update = time.ticks_ms()

        elif cmd.startswith("P="):
            p = cmd[2:].split(',')
            gps_spd, gps_hdg, gps_alt, gps_acc = map(float, p)
            last_gps_update = time.ticks_ms()

        elif '=' in cmd:
            p = cmd.split('=')
            if p[0].isdigit():
                idx = int(p[0]) - 1
                val = int(p[1])
                if 0 <= idx < 8:
                    can_state[idx] = val
                    safe_can_send(can_tx_id, can_state)
                    ble_tx_queue.append(("STATE=" + ",".join(str(b) for b in can_state)).encode())
    except: pass

def process_can_rx():
    global can_error, can_rx_count, can_bus_active
    if can is None: return
    try:
        for _ in range(DRAIN_MAX):
            if can.any(0) == 0: break
            msg = can.recv(0, timeout=0)
            if not msg: break
            can_id = msg[0] & 0x7FF
            if can_id not in allowed_ids_set: continue
            can_rx_count += 1
            can_bus_active = True
            data = msg[4]
            if can_id == CAN_GROUP_1_ID:
                for i in range(4):
                    val = extract_val(data, i * 2, slot_modes[i])
                    if val is not None:
                        last_vals[i] = val
            elif can_id == CAN_GROUP_2_ID:
                for i in range(3):
                    val = extract_val(data, i * 2, slot_modes[i + 4])
                    if val is not None:
                        last_vals[i + 4] = val
        can_error = False
    except MemoryError: pass
    except: can_error = True

def send_vals_packet(uart):
    if not last_vals: return
    parts = []
    for i in range(7):
        v = last_vals.get(i)
        parts.append("" if v is None else str(v))
    while parts and parts[-1] == "":
        parts.pop()
    if not parts: return
    msg = "VALS=" + ",".join(parts)
    try:
        uart.send(msg.encode())
    except: pass

# ------------------------------
# 初期化
# ------------------------------
M5.begin()
try:
    nvs = NVS("can_app")
    CAN_GROUP_1_ID = nvs.get_i32("grp1_id")
    CAN_GROUP_2_ID = nvs.get_i32("grp2_id")
    can_tx_id      = nvs.get_i32("my_id")
    k_meter_id     = nvs.get_i32("k_meter_id")
except: pass
try:
    _v = nvs.get_i32("gps_base_id")
    if _v is not None: gps_base_id = _v
except: pass
try:
    for i in range(7): slot_modes[i] = nvs.get_i32(f"slot{i}_mode")
except: pass

# ★ PIN読み込み
_load_pin()

try:
    for i in range(8):
        ov = nvs.get_i32(f"btn_off_{i}")
        if ov is not None:
            can_state[i] = ov
except: pass

try:
    can = CANUnit(0, port=(TX_PIN, RX_PIN), mode=CANUnit.NORMAL, baudrate=CAN_BAUDRATE)
    time.sleep_ms(100)
    update_hw_filter()
    print("CAN Init OK")
except Exception as e:
    print("CAN Init Fail:", e)

try:
    i2c = I2C(0, scl=Pin(1), sda=Pin(2), freq=100000)
    kmeter_found = (0x66 in i2c.scan())
except: pass

ble  = bluetooth.BLE()
uart = BLEUART(ble)
M5.Display.setTextSize(2)
M5.Display.clear()

# ------------------------------
# メインループ
# ------------------------------
while True:
    M5.update()
    now = time.ticks_ms()

    process_ble_cmd()

    if _pending_config_send:
        _pending_config_send = False
        ble_tx_queue.append(b"__SYNC_DELAY__")

    process_can_rx()

    if time.ticks_diff(now, last_can_send) > CAN_SEND_INT:
        safe_can_send(can_tx_id, can_state)
        last_can_send = now

    if time.ticks_diff(now, last_gps_send) > GPS_SEND_INT:
        if time.ticks_diff(now, last_gps_update) < 3000:
            send_gps_can()
        last_gps_send = now

    if time.ticks_diff(now, last_temp_send) > TEMP_SEND_INT:
        if kmeter_found:
            try:
                d = i2c.readfrom_mem(0x66, 0x00, 4)
                t = int(struct.unpack('<i', d)[0] / 100.0)
                last_temp_val = t
                s_data = bytearray([0x01, 1 if t >= 0 else 0,
                                    (abs(t) >> 8) & 0xFF, abs(t) & 0xFF,
                                    0, 0, 0, 0])
                safe_can_send(k_meter_id, s_data)
                ble_tx_queue.append(f"TEMP={t}".encode())
            except: pass
        last_temp_send = now

    if ble_tx_queue:
        item = ble_tx_queue.pop(0)
        if item == b"__SYNC_DELAY__":
            time.sleep_ms(300)
            queue_config_sync()
        else:
            try: uart.send(item)
            except: pass
    elif time.ticks_diff(now, last_vals_send) >= VALS_SEND_INT:
        send_vals_packet(uart)
        last_vals_send = now

    if time.ticks_diff(now, last_display) > DISP_INT:
        check_can_recovery()
        if can_error: ble_tx_queue.append(b"STATUS=ERR")
        elif not can_bus_active: ble_tx_queue.append(b"STATUS=NO_BUS")
        else: ble_tx_queue.append(b"STATUS=CAN_OK")
        M5.Display.setCursor(0, 0)
        M5.Display.setTextColor(0xFFFF, 0x0000)
        # CAN BUSステータス
        if can_error:
            M5.Display.setTextColor(0xF800, 0x0000)
            M5.Display.print("V8.1 CAN:ERR")
        elif can_bus_active:
            M5.Display.setTextColor(0x07E0, 0x0000)
            M5.Display.print("V8.1 BUS:OK ")
        else:
            M5.Display.setTextColor(0x8410, 0x0000)
            M5.Display.print("V8.1 BUS:-- ")
        M5.Display.setCursor(0, 20)
        M5.Display.setTextColor(0x07E0 if filter_ok else 0xF800, 0x0000)
        M5.Display.print("FLT:%s  " % ("HW" if filter_ok else "SW"))
        M5.Display.setCursor(0, 40)
        M5.Display.setTextColor(0xFFFF, 0x0000)
        M5.Display.print("T:%d Q:%d  " % (last_temp_val, len(ble_tx_queue)))
        # PINステータス
        M5.Display.setCursor(0, 60)
        if pin_code is None:
            M5.Display.setTextColor(0xF800, 0x0000)
            M5.Display.print("PIN:---  ")
        elif pin_verified:
            M5.Display.setTextColor(0x07E0, 0x0000)
            M5.Display.print("PIN:AUTH ")
        else:
            M5.Display.setTextColor(0xFFE0, 0x0000)
            M5.Display.print("PIN:LOCK ")
        last_display = now

    time.sleep_ms(1)
