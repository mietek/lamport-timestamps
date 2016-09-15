{-

https://github.com/mietek/lamport-timestamps

An Agda formalisation of Lamport timestamps.

Made by Miëtek Bak.  Published under the MIT X11 license.

-}

module Everything where

import Prelude


-- Processes, clocks, timestamps, messages, and events are defined as abstract interfaces.

import AbstractInterfaces
import BasicConcreteImplementations


-- Lamport’s clock condition yields a strict total order on events across all processes.

import OrdersAndEqualities
