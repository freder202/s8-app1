---------------------------------------------------------------------------------------------
--	Author :    Marc-Andre Tetrault
--  Project :   Verification Primer
--
--  Universite de Sherbrooke, 2017
---------------------------------------------------------------------------------------------

---------------------------------------------------------------------------------------------
--	Library and Package Declarations
---------------------------------------------------------------------------------------------
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.numeric_std.ALL;

---------------------------------------------------------------------------------------------
--	Entity Declaration
---------------------------------------------------------------------------------------------
entity CommonModules is
port(
    reset               : in std_logic;
	clk					: in std_logic;

    uart_in             : in std_logic;
    uart_out            : out std_logic;

    userif_Mode         : in std_logic_vector(1 downto 0);
    userif_Addr         : in std_logic_vector(5 downto 0);
    userif_DataIn       : in std_logic_vector(7 downto 0);
    userif_DataOut      : out std_logic_vector(7 downto 0);
    userif_SampleRead	: in std_logic;
    userif_SampleEmpty	: out std_logic;
    userif_SampleData	: out std_logic_vector(15 downto 0);


    chan_ReadSample0		: out std_logic;
    chan_ReadSample1		: out std_logic;
    chan_ReadSampleEmpty0	: in std_logic;
    chan_ReadSampleEmpty1	: in std_logic;
    chan_ReadSampleData		: in std_logic_vector(15 downto 0);

    reg_Mode            : out std_logic_vector(1 downto 0);
    reg_Addr            : out std_logic_vector(5 downto 0);
    reg_DataIn          : out std_logic_vector(7 downto 0);
    reg_DataOut         : in std_logic_vector(7 downto 0);

    o_MasterEnable      : out std_logic    -- assertion says must come up 4 clocks or more before channel enable.
	);
end CommonModules;

---------------------------------------------------------------------------------------------
--	Object declarations
---------------------------------------------------------------------------------------------
architecture Behavioral of CommonModules is

--	Components
component CommonRegisters is
port(
    reset               : in std_logic;
	clk					: in std_logic;

    i_Mode              : in std_logic_vector(1 downto 0);
    i_Addr              : in std_logic_vector(5 downto 0);
    i_DataIn            : in std_logic_vector(7 downto 0);
    o_DataOut           : out std_logic_vector(7 downto 0);

    o_MasterEnable      : out std_logic;
    o_DebugWaveOutput   : out std_logic
	);
end component;

component CommandInterface is
port(
	reset    			: in std_logic;
	clk					: in std_logic;

	-- Description
    i_UartMessage       : in std_logic;
    i_UartMessagePacket : in std_logic_vector(15 downto 0);
    o_UartReplyGo       : out std_logic;
    i_UartReplyAck		: in std_logic;
    o_UartReplyPacket   : out std_logic_vector(15 downto 0);


    i_UserIfMessage       : in std_logic;
    o_UserIfMessageAck    : out std_logic;
    o_UserIfBusy          : out std_logic;
    i_UserIfMessagePacket : in std_logic_vector(15 downto 0);
    o_UserIfReplyPacket   : out std_logic_vector(15 downto 0);

    reg_Mode            : out std_logic_vector(1 downto 0);
    reg_Addr            : out std_logic_vector(5 downto 0);
    reg_DataIn          : out std_logic_vector(7 downto 0);
    reg_DataOut         : in std_logic_vector(7 downto 0)

	);
end component;

component SerialReceiver is
port(
	reset    			: in std_logic;
	clk					: in std_logic;
	i_keepfailedparity	: in std_logic;
	i_serialdata		: in std_logic;
	o_pdata_avail		: out std_logic;
	o_parityerror		: out std_logic;
	o_pdata				: out std_logic_vector(15 downto 0)
	);
end component;

component SerialTransmitter is
port(
	reset   				: in std_logic;
	clk						: in std_logic;
	i_pdata					: in std_logic_vector(15 downto 0);
	i_pdata_load			: in std_logic;
	o_engineready_loadack	: out std_logic;  -- ready when high, ack_tx/busy when low
	o_serialdata			: out std_logic
	);
end component;

component SynchFifo is
port(
	reset				: in std_logic;
	clk					: in std_logic;

	-- Write Port
	i_WrEn				: in std_logic;
	i_WrData			: in std_logic_vector(15 downto 0);
	o_HalfFull			: out std_logic;
	o_Full				: out std_logic;

	-- Read Port
	i_RdEn				: in std_logic;
	o_RdData			: out std_logic_vector(15 downto 0);
	o_Empty				: out std_logic
	);
end component;

component TransmitterControl is
port(
	reset    			: in std_logic;
	clk					: in std_logic;

	-- Description
    i_UartReplyGo       : in std_logic;
    o_UartReplyAck		: out std_logic;
    i_UartReplyPacket 	: in std_logic_vector(15 downto 0);

    i_DebugSampleEmpty	: in std_logic;
    o_DebugSampleRead   : out std_logic;
    i_DebugSampleValue  : in std_logic_vector(15 downto 0);

    o_UartTxGo       	: out std_logic;
    i_UartTxDone     	: in std_logic;
    o_UartTxPacket   	: out std_logic_vector(15 downto 0)
	);
end component;


--	User types and State Machines

--	Convenient constants
constant c_one  : std_logic := '1';
constant c_zeros    : std_logic_vector(15 downto 0) := X"0000";

--	Signals
signal s_Mode              : std_logic_vector(1 downto 0);
signal s_Addr              : std_logic_vector(5 downto 0);
signal s_DataIn            : std_logic_vector(7 downto 0);
signal s_DataOut           : std_logic_vector(7 downto 0);
signal cmn_DataOut           : std_logic_vector(7 downto 0);

signal s_MasterEnable      : std_logic;
signal s_DebugWaveOutput   : std_logic;

signal s_uartmessage        : std_logic;
signal s_uartmessagepacket  : std_logic_vector(15 downto 0);


signal s_UartReplyGo        : std_logic;
signal s_UartReplyAck		: std_logic;
signal s_UartReplyPacket    : std_logic_vector(15 downto 0);


signal s_DebugSampleEmpty	: std_logic;
signal s_DebugSampleRead	: std_logic;
signal s_DebugSampleValue	: std_logic_vector(15 downto 0);
signal s_UartGo				: std_logic;
signal s_UartDone			: std_logic;
signal s_UartPacket			: std_logic_vector(15 downto 0);


--	Registers


-- Attributes

begin

u_CommandInterface : CommandInterface
port map(
	reset    			    => reset,
	clk					    => clk,

	-- Description
    i_UartMessage           => s_uartmessage,
    i_UartMessagePacket     => s_uartmessagepacket,
    o_UartReplyGo           => s_UartReplyGo,
    i_UartReplyAck			=> s_UartReplyAck,
    o_UartReplyPacket       => s_UartReplyPacket,

    i_UserIfMessage         => c_zeros(0),
    o_UserIfMessageAck      => open,
    o_UserIfBusy            => open,
    i_UserIfMessagePacket   => c_zeros,
    o_UserIfReplyPacket     => open,

    reg_Mode                => s_Mode,
    reg_Addr                => s_Addr,
    reg_DataIn              => s_DataIn,
    reg_DataOut             => s_DataOut
	);


u_CommonRegisters : CommonRegisters
port map(
    reset               => reset,
	clk					=> clk,

    i_Mode              => s_Mode,
    i_Addr              => s_Addr,
    i_DataIn            => s_DataIn,
    o_DataOut           => cmn_DataOut,

    o_MasterEnable      => s_MasterEnable,
    o_DebugWaveOutput   => s_DebugWaveOutput
	);


   o_MasterEnable      <= s_MasterEnable;


---------------------------------------------------------------------------------------------
--	Triggered event buffering
---------------------------------------------------------------------------------------------
u_BufferingControl : block
	signal s_ReadSampleFifo		: std_logic_vector(1 downto 0);
	signal s_FifoWrite			: std_logic;
	signal s_FifoHalfFull		: std_logic;
	signal s_FifoReadSignal		: std_logic;
	signal s_FifoEmpty			: std_logic;
	signal s_FifoData			: std_logic_vector(15 downto 0);

	signal r_SamplesCount		: unsigned(7 downto 0) := X"00";
	signal r_SourceSelect		: std_logic;
	signal r_FifoWrite			: std_logic;
begin

	-- To Fifo
	s_FifoReadSignal 	<= (userif_SampleRead and not s_DebugWaveOutput)
						 or (s_DebugSampleRead and s_DebugWaveOutput);
	-- From Fifo
	userif_SampleData	<= s_FifoData;
	userif_SampleEmpty	<= s_FifoEmpty and not s_DebugWaveOutput;

    s_DebugSampleEmpty	<= s_FifoEmpty and s_DebugWaveOutput;
    s_DebugSampleValue  <= s_FifoData;

	u_SynchFifo : SynchFifo
	port map(
		reset				=> reset,
		clk					=> clk,

		-- Write Port
		i_WrEn				=> r_FifoWrite,
		i_WrData			=> chan_ReadSampleData,
		o_HalfFull			=> s_FifoHalfFull,
		o_Full				=> open,

		-- Read Port
		i_RdEn				=> s_FifoReadSignal,
		o_RdData			=> s_FifoData,
		o_Empty				=> s_FifoEmpty
		);

	process(clk)
	begin
		if(clk'event and clk = '1') then
			if(reset = '1') then
				r_SamplesCount <= X"00";
				r_SourceSelect <= '0';
			elsif(r_SamplesCount /= X"00") then
				r_SamplesCount <= r_SamplesCount - 1;
			elsif(chan_ReadSampleEmpty1 = '0' and s_FifoHalfFull = '0') then
				r_SourceSelect <= '1';
				r_SamplesCount <= X"10";
			elsif(chan_ReadSampleEmpty0 = '0' and s_FifoHalfFull = '0') then
				r_SourceSelect <= '0';
				r_SamplesCount <= X"10";
			end if;

			if(reset = '1') then
				r_FifoWrite <= '0';
			else
				r_FifoWrite <= s_FifoWrite;
			end if;
		end if;
	end process;

	s_ReadSampleFifo(0) <= '1' when r_SamplesCount /= X"00" and r_SourceSelect = '0' else '0';
	s_ReadSampleFifo(1) <= '1' when r_SamplesCount /= X"00" and r_SourceSelect = '1' else '0';

	s_FifoWrite <= s_ReadSampleFifo(1) or s_ReadSampleFifo(0);

	chan_ReadSample0 <= s_ReadSampleFifo(0);
	chan_ReadSample1 <= s_ReadSampleFifo(1);
end block;



---------------------------------------------------------------------------------------------
--	Channel and Common register controls and mux
---------------------------------------------------------------------------------------------

-- send register commands to channels
reg_Mode    <= s_Mode;
reg_Addr    <= s_Addr;
reg_DataIn  <= s_DataIn;

-- mux between channels and common
process(s_Addr, reg_DataOut, cmn_DataOut )
begin
    if (s_Addr(5) = '1') then
        s_DataOut <= cmn_DataOut;
    else
        s_DataOut <= reg_DataOut;
    end if;
end process;


---------------------------------------------------------------------------------------------
--	UART
---------------------------------------------------------------------------------------------
u_SerialReceiver : SerialReceiver
port map(
	reset               => reset,
	clk                 => clk,
	i_keepfailedparity	=> c_one,
	i_serialdata		=> uart_in,
	o_pdata_avail		=> s_uartmessage,
	o_parityerror		=> open,
	o_pdata				=> s_uartmessagepacket
	);

u_TransmitterControl : TransmitterControl
port map(
	reset    			=> reset,
	clk					=> clk,

	-- Description
    i_UartReplyGo       => s_UartReplyGo,
    o_UartReplyAck		=> s_UartReplyAck,
    i_UartReplyPacket 	=> s_UartReplyPacket,

    i_DebugSampleEmpty	=> s_DebugSampleEmpty,
    o_DebugSampleRead   => s_DebugSampleRead,
    i_DebugSampleValue  => s_DebugSampleValue,

    o_UartTxGo       	=> s_UartGo,
    i_UartTxDone     	=> s_UartDone,
    o_UartTxPacket   	=> s_UartPacket
	);

u_SerialTransmitter : SerialTransmitter
port map(
	reset					=> reset,
	clk						=> clk,
	i_pdata					=> s_UartPacket,
	i_pdata_load			=> s_UartGo,
	o_engineready_loadack	=> s_UartDone,
	o_serialdata			=> uart_out
	);

end Behavioral;
