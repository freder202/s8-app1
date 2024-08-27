import cocotb
from cocotb.clock import Clock
from cocotb.triggers import Join
from cocotbext.uart import UartSource, UartSink
from utilsVerif import *
from cocotb.log import SimLog


# Decorator to tell cocotb this function is a coroutine
@cocotb.test()
async def cocotbext_uart_demo(dut):
    print("Uart instance demo")
    await init(dut)

    # L2.E1 - Ajouter l'instanciation du MMC
    # inst_MMC_CRC8 = MMC_CRC8(dut.CheminVersPacketMergerCRC8)
    # await inst_MMC_CRC8.start()

    # L1.E4 - Ajouter l'initialisation des pattes d'entrée et de l'horloge
    # await votre_initialisation(dut) 

    # Driver and Sink for the dut UART RX/TX channels
    uart_driver = UartSource(dut.in_sig, baud=1000000, bits=8)
    uart_sink   = UartSink(dut.out_sig, baud=1000000, bits=8)

    # L1.E4 - Start thread for the reply function for the expected UART response.
    # Task_returnMessage = await cocotb.start(wait_reply(dut, uart_sink))

    # Generate arbitrary value to send on the UART
    # SomeValue = cocotb.binary.BinaryValue(value=0xDEADBEEF, n_bits=32, bigEndian=True)
    SomeValue = build_command_message(0,0x9,0)
    # Print cocotb value demo function. Uncomment if desired.
    # print_cocotb_BinaryValue(SomeValue)

    # Send arbitrary value, then wait for transaction to complete
    await uart_driver.write(SomeValue.buff)
    await uart_driver.wait()

    # L1.E4 ait for response to complete or for timeout
    # await Task_returnMessage


async def init(dut):
    dut.reset.value = 1
    dut.in_sig.value = 1
    dut.resetCyclic.value = 1
    dut.sipms.value = 3
    # fetch value from a signal in the dut
    fetch_value = dut.reset.value
    # Confirm type of read signal. Expected: cocotb.binary.BinaryValue
    print(type(fetch_value))
    await cocotb.start(Clock(dut.clk, 10, units='ns').start())
    # wait for 1000 clock periods
    await cocotb.triggers.ClockCycles(dut.clk, 10, rising=True)
    dut.reset.value = 0
    await cocotb.triggers.ClockCycles(dut.clk, 1, rising=True)


# L.E4 function to wait for response message
async def wait_reply(dut, uart_sink):

    # Non-infinite wait loop. Throw cocotb exception if timeout is reached (to do)
    for x in range(0, 100):
        if(uart_sink.count() >= 7): ## 6 octets du message + le CRC
            break;
        await cocotb.triggers.ClockCycles(dut.clk, 1000, rising=True)

    if(x == 99):
        print("Timeout")
        logger = SimLog("cocotb.Test")
        logger.info("Timeout for wait reply")
        raise RuntimeError("Timeout for wait reply")
        # or use plain assert.
        #assert False, "Timeout for wait reply"
        return None

    else:
        # cocotbext-uart returns byteArray. Convert to bytes first, then to Binary value for uniformity.
        message_bytes = bytes(await uart_sink.read(count=6))
        message = cocotb.binary.BinaryValue(value=message_bytes, n_bits=48, bigEndian=False)
        print("After a wait of " + str(x) + "000 clocks, received message: ", end='')
        print("0x{0:0{width}x}".format(message.integer, width=12))
        return message


