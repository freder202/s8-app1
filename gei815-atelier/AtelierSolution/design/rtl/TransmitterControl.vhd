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
entity TransmitterControl is
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
end TransmitterControl;

---------------------------------------------------------------------------------------------
--	Object declarations
---------------------------------------------------------------------------------------------
architecture Behavioral of TransmitterControl is

--	Components

--	User types and State Machines
type fsmt_TransmitControl is
(
	sta_Idle,

	sta_CommandReply,
	sta_CommandWaitAck,

	sta_SampleTransmit,
	sta_SampleWaitAck
);

signal fsm_TransmitControl : fsmt_TransmitControl := sta_Idle;

--	Convenient constants

--	Signals
signal s_UartTxGo       	: std_logic;

--	Registers
signal r_UartMessagePresent     : std_logic;

signal r_SampleCounter	        : unsigned(3 downto 0);
signal r_UartTxPacket	        : std_logic_vector(15 downto 0);


signal r_ReplyPacket            : std_logic_vector(15 downto 0);
signal r_UserIf_nUart           : std_logic;
signal r_SendBackUart           : std_logic;
signal r_DebugSampleRead    	: std_logic;
signal r_UartReplyAck			: std_logic;

-- Attributes

begin

process(clk)
begin
	if (clk'event and clk = '1')then
        if(reset = '1') then
            fsm_TransmitControl <= sta_Idle;
            r_SampleCounter <= (others => '0');
            r_UartReplyAck <= '0';
            r_DebugSampleRead <= '0';
        else
			r_UartReplyAck <= '0'; -- default
            r_DebugSampleRead <= '0';

		    case fsm_TransmitControl is
			    when sta_Idle =>
                    if(i_UartReplyGo = '1') then
                        fsm_TransmitControl <= sta_CommandReply;
                        r_UartTxPacket <= i_UartReplyPacket;

                    elsif(i_DebugSampleEmpty = '0') then
                        fsm_TransmitControl <= sta_SampleTransmit;
						r_UartTxPacket <= i_DebugSampleValue;
                    end if;

                when sta_CommandReply =>
                    fsm_TransmitControl <= sta_CommandWaitAck;

                when sta_CommandWaitAck =>
					if(i_UartTxDone = '1') then
						fsm_TransmitControl <= sta_Idle;
						r_UartReplyAck <= '1';
					end if;



                when sta_SampleTransmit =>
                    fsm_TransmitControl <= sta_SampleWaitAck;
                    -- strobe before SampleWaitAck,
                    -- so empty is up to date we reach idle
					r_DebugSampleRead <= '1';

                when sta_SampleWaitAck =>
					if(i_UartTxDone = '1') then
						fsm_TransmitControl <= sta_Idle;
						r_SampleCounter <= r_SampleCounter + 1;
					end if;

                when others =>
                    fsm_TransmitControl <= sta_Idle;
            end case;
        end if;
    end if;
end process;


o_UartTxPacket		<= r_UartTxPacket;
s_UartTxGo			<= '1' when fsm_TransmitControl = sta_CommandReply or sta_SampleTransmit = sta_CommandReply else '0';
o_UartTxGo			<= s_UartTxGo;
o_DebugSampleRead	<= r_DebugSampleRead;
o_UartReplyAck		<= r_UartReplyAck;




end Behavioral;
