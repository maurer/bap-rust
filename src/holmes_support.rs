//! This module provides `holmes` `Value` and `Type` status for selected binary analysis types, to
//! ease the use of this library in conjunction with `holmes`
use holmes::pg::dyn::values::ValueT;
use holmes::pg::dyn::types::TypeT;
use high::bitvector::BitVector;
use basic::Arch;
use std::any::Any;
use std::sync::Arc;
use postgres::types::ToSql;
use holmes::pg::RowIter;
use holmes::pg::dyn::{Type, Value};
use holmes::pg::dyn::values::ToValue;
use num::traits::FromPrimitive;

#[derive(Debug,Clone,Hash,PartialEq)]
/// This type is used to give a `holmes` `Type` to `bap::bitvector::BitVector`
pub struct BitVectorType;
impl TypeT for BitVectorType {
    fn name(&self) -> Option<&'static str> {
        Some("bitvector")
    }
    fn extract(&self, cols: &mut RowIter) -> Option<Value> {
        cols.next().map(|col| Arc::new(BitVector::new(&col)) as Value)
    }
    fn repr(&self) -> Vec<String> {
        vec!["bit varying".to_string()]
    }
    typet_boiler!();
}

impl ValueT for BitVector {
    fn type_(&self) -> Type {
        Arc::new(BitVectorType)
    }
    fn get(&self) -> &Any {
        self as &Any
    }
    fn to_sql(&self) -> Vec<&ToSql> {
        vec![self.to_bitvec()]
    }
    valuet_boiler!();
}

impl ToValue for BitVector {
    fn to_value(self) -> Value {
        Arc::new(self)
    }
}

#[derive(Debug,Clone,Hash,PartialEq)]
/// This type is used to give a `holmes` `Type` to `bap::basic::Arch`
pub struct ArchType;
impl TypeT for ArchType {
    fn name(&self) -> Option<&'static str> {
        Some("arch")
    }
    fn extract(&self, cols: &mut RowIter) -> Option<Value> {
        cols.next().and_then(|col| Arch::from_i16(col).map(|arch| Arc::new(arch) as Value))
    }
    fn repr(&self) -> Vec<String> {
        vec!["SMALLINT".to_string()]
    }
    typet_boiler!();
}

impl ValueT for Arch {
    fn type_(&self) -> Type {
        Arc::new(ArchType)
    }
    fn get(&self) -> &Any {
        self as &Any
    }
    fn to_sql(&self) -> Vec<&ToSql> {
        vec![self.i16_ref()]
    }
    valuet_boiler!();
}

impl ToValue for Arch {
    fn to_value(self) -> Value {
        Arc::new(self)
    }
}
